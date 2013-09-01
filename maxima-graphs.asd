;;; -*- Mode: lisp -*-

(defsystem maxima-graphs
  :description "The graphs package of Maxima, made standalone."
  :licence "GPLv3"
  :depends-on (alexandria)
  :serial t
  :components
  ((:file "packages")
   (:file "maximal")
   (:file "graph-core")
   (:file "spring-embedding")
   (:file "isomorphism")
   (:file "matching")
   (:file "graph6")
   (:file "demoucron")
   (:file "dijkstra")
   (:file "wiener-index")))

