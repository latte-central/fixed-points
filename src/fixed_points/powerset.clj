;; gorilla-repl.fileformat = 1

;; **
;;; # The powerset in type theory
;;; 
;;; There is a non-trivial issue when trying to encode the notion of a powerset in a type theory such as the one implemented in LaTTe.
;;; But the notion is quite important for the application of the fixed point theory developed in this project.
;; **

;; @@
(ns fixed-points.powerset
  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom
                                          forall lambda ==>
                                          assume have proof lambda]])

  (:require [latte.quant :as q :refer [exists]])

  (:require [latte.prop :as p :refer [<=> and or not]])

  (:require [latte.equal :as eq :refer [equal]])
  
  (:require [latte.rel :as rel :refer [rel]])
  
  (:require [latte-sets.core :as set :refer [set elem]])
)
;; @@
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; **
;;; In the set theory we develop in `latte-sets`, a set of element of type `T` is of type `(==> T :type)` that we abbreviate as `(set T)`. 
;;; This is a *predicate* characterizing a subset of `T`. An element of type `T` is in a set `S` iff `(S x)` (which we also denote by `(elem T x S)`).
;;; Despite being quite effective in practice, this approach has one notable drawback: a *set* `S` is a function and not a type itself. For example, one cannot write something like `(forall [x S] (P x))` since `S` is not a type. The replacement is `(forall [x T] (==> (elem T x S) (P x)))`.
;;; 
;;; Now the first question we might ask is:
;;; 
;;; > How do we encode a set of sets ?
;; **

;; @@
(definition SET
  "A set of sets constructor."
 [[T :kind]]
 (==> T :type))
;; @@
;; ->
;;; [Warning] redefinition as term:  SET
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>SET</span>","value":"SET"}],"value":"[:defined :term SET]"}
;; <=

;; @@
(latte/type-of [S :type] (set S))
;; @@
;; =>
;;; {"type":"html","content":"<span class='clj-symbol'>□</span>","value":"□"}
;; <=

;; @@
(latte/term [S :type] (SET (set S)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-list'>(</span>","close":"<span class='clj-list'>)</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-var'>#&#x27;fixed-points.powerset/SET</span>","value":"#'fixed-points.powerset/SET"},{"type":"list-like","open":"<span class='clj-list'>(</span>","close":"<span class='clj-list'>)</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-var'>#&#x27;latte-sets.core/set</span>","value":"#'latte-sets.core/set"},{"type":"html","content":"<span class='clj-symbol'>S</span>","value":"S"}],"value":"(#'latte-sets.core/set S)"}],"value":"(#'fixed-points.powerset/SET (#'latte-sets.core/set S))"}
;; <=

;; @@
(latte/type-of [S :type] (SET (set S)))
;; @@
;; =>
;;; {"type":"html","content":"<span class='clj-symbol'>□</span>","value":"□"}
;; <=

;; @@

;; @@
