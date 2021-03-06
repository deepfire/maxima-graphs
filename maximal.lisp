;;;
;;;  GRAPHS - graph theory package for Maxima
;;;
;;;  Copyright (C) 2007 Andrej Vodopivec <andrej.vodopivec@gmail.com>
;;;
;;;  This program is free software; you can redistribute it and/or modify
;;;  it under the terms of the GNU General Public License as published by
;;;  the Free Software Foundation; either version 2 of the License, or	 
;;;  (at your option) any later version. 
;;;
;;;  This program is distributed in the hope that it will be useful,
;;;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;;  GNU General Public License for more details.
;;;
;;;  You should have received a copy of the GNU General Public License
;;;  along with this program; if not, write to the Free Software
;;;  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
;;;
(in-package :maxima-graphs)

;; flags hardwiring:
; $inflag:       false
; $partswitch:   false
; $sqrtdispflag: false

;; comm.lisp
(defun $append (&rest args)
  (if (null args)
      '((mlist simp))
      (let ((arg1 (specrepcheck (first args))) op arrp)
	(atomchk arg1 '$append nil)
	(setq op (mop arg1)
	      arrp (if (member 'array (cdar arg1) :test #'eq) t))
	(mcons-exp-args
	 arg1
	 (apply #'append
		(mapcar #'(lambda (u)
			    (atomchk (setq u (specrepcheck u)) '$append nil)
			    (unless (and (alike1 op (mop u))
					 (eq arrp (if (member 'array (cdar u) :test #'eq) t)))
			      (merror "append: operators of arguments must all be the same."))
			    (margs u))
			args))))))

(defun $rest (e &optional (n 1 n?))
  (prog (m fun fun1 revp)
     (when (and n? (equal n 0))
       (return e))
     (atomchk (setq m (format1 e)) '$rest nil)
     (cond ((and n? (not (fixnump n)))
	    (merror "rest: second argument, if present, must be an integer; found ~M" n))
	   ((minusp n)
	    (setq n (- n) revp t)))
     (if (< (length (margs m)) n)
	 (merror "rest: fell off the end."))
     (setq fun (car m))
     (when (eq (car fun) 'mqapply)
       (setq fun1 (cadr m)
	     m (cdr m)))
     (setq m (cdr m))
     (when revp (setq m (reverse m)))
     (setq m (nthcdr n m))
     (setq m (cons (if (eq (car fun) 'mlist) fun (delsimp fun))
		   (if revp (nreverse m) m)))
     (when (eq (car fun) 'mqapply)
       (return (cons (car m) (cons fun1 (cdr m)))))
     (return m)))

(defun $first (e)
  (atomchk (setq e (format1 e)) '$first nil)
  (if (null (cdr e)) (merror "first: empty argument."))
  (car (margs e)))

(defun $second (e)
  (atomchk (setq e (format1 e)) 'first nil)
  (if (< (length (margs e)) 2)
      (merror "~:M: no such element in ~M" 'second e))
  (second (margs e)))

(defun $length (e)
  (setq e (cond (($listp e) e)
		((not ($ratp e)) (specrepcheck e))
		(t ($ratdisrep e))))
  (cond ((symbolp e) (merror "length: argument cannot be a symbol; found ~:M" e))
	((or (numberp e) (eq (caar e) 'bigfloat))
	 (if (mnegp e)
	     1
	     (merror "length: argument cannot be a number; found ~:M" e)))
	((not (member (caar e) '(mtimes mexpt) :test #'eq)) (length (margs e)))
	((eq (caar e) 'mexpt)
	 2)
	(t (length (cdr (nformat e))))))

(defun $listp (x)
  (and (not (atom x))
       (not (atom (car x)))
       (eq (caar x) 'mlist)))

(defun $float (e)
  (cond ((numberp e) (float e))
	((and (symbolp e) (mget e '$numer)))
	((or (atom e) (member 'array (cdar e) :test #'eq)) e)
	((eq (caar e) 'rat) (fpcofrat e))
	((eq (caar e) 'bigfloat) (fp2flo e))
	((member (caar e) '(mexpt mncexpt) :test #'eq)
	 ;; avoid x^2 -> x^2.0, allow %e^%pi -> 23.14
	 (let ((res (recur-apply #'$float e)))
	   (if (floatp res)
	       res
	       (list (ncons (caar e)) ($float (cadr e)) (caddr e)))))
	((and (eq (caar e) '%log)
	      (complex-number-p (second e) '$ratnump))
	 ;; Basically we try to compute float(log(x)) as directly as
	 ;; possible, expecting Lisp to return some error if it can't.
	 ;; Then we do a more complicated approach to compute the
	 ;; result.  However, gcl and ecl don't signal errors in these
	 ;; cases, so we always use the complicated approach for these lisps.
	 (let ((n (second e)))
	   (cond ((integerp n)
		  ;; float(log(int)).  First try to compute (log
		  ;; (float n)).  If that works, we're done.
		  ;; Otherwise we need to do more.  
		  (to (or (try-float-computation #'(lambda ()
						     (log (float n))))
			  (let ((m (integer-length n)))
			    ;; Write n as (n/2^m)*2^m where m is the number of
			    ;; bits in n.  Then log(n) = log(2^m) + log(n/2^m).
			    ;; n/2^m is approximately 1, so converting that to a
			    ;; float is no problem.  log(2^m) = m * log(2).
			    (+ (* m (log 2e0))
			       (log (float (/ n (ash 1 m)))))))))
		 (($ratnump n)
		  ;; float(log(n/m)) where n and m are integers.  Try computing
		  ;; it first.  If it fails, compute as log(n) - log(m).
		  (let ((try (try-float-computation #'(lambda() 
							(log (fpcofrat n))))))
		    (if try
			(to try)
			(sub  ($float `((%log) ,(second n)))
			      ($float `((%log) ,(third n)))))))
		 ((complex-number-p n 'integerp)
		  ;; float(log(n+m*%i)).
		  (let ((re ($realpart n))
			(im ($imagpart n)))
		    (to (or (try-float-computation #'(lambda ()
						       (log (complex (float re)
								     (float im)))))
			    (let* ((size (max (integer-length re)
					      (integer-length im)))
				   (scale (ash 1 size)))
			      (+ (* size (log 2e0))
				 (log (complex (float (/ re scale))
					       (float (/ im scale))))))))))
		 (t
		  ;; log(n1/d1 + n2/d2*%i) =
		  ;;   log(s*(n+m*%i)) = log(s) + log(n+m*%i)
		  ;;
		  ;; where s = lcm(d1, d2), n and m are integers
		  ;;
		  (let* ((s (lcm ($denom ($realpart n))
				 ($denom ($imagpart n))))
			 (p ($expand (mul s n))))
		    (add ($float `((%log) ,s))
			 ($float `((%log) ,p))))))))
	((and (eq (caar e) '%erf)
	      (eq (second e) '$%i))
	 ;; Handle like erf(%i).  float(%i) (via recur-apply below)
	 ;; just returns %i, so we never numerically evaluate it.
	 (complexify (complex-erf (complex 0 1d0))))
	(t (recur-apply #'$float e))))

;; merror.lisp
(defun $error (&rest l)
  "Signals a Maxima user error."
  (apply #'error l))

;; simp.lisp
(defun $abs (x)
  (abs x))

;; mlisp.lisp
(defun $sin (x)
  (sin x))

(defun $cos (x)
  (cos x))
