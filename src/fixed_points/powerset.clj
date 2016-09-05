;; gorilla-repl.fileformat = 1

;; **
;;; # Fixed points for powerset inclusion
;;; 
;;; In this document we provide a demonstration of the least/greatest fixed point theorems for monotone functions on *powerset inclusion*, i.e. the sets of sets ordered according to the subset relation. This is one of the most important practical setting for the fixed point theorems (at least in computer science).
;; **

;; @@
(ns fixed-points.powerset
  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom
                                          forall lambda ==>
                                          assume have proof lambda]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]
            [latte.rel :as rel :refer [rel]]
            [latte-sets.core :as set :refer [set elem
                                             subset seteq]]))
;; @@
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(use 'clojure.repl)
;; @@
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; **
;;; ## The subset ordering
;;; 
;;; We begin by surveing some basic properties of the subset ordering.
;;; 
;;; First, the subset relation is a partial order: it is reflexive, transitive and antisymmetric (wrt. set equality `seteq`).
;; **

;; @@
(source subset)
;; @@
;; ->
;;; (definition subset
;;;   &quot;The subset relation for type `T`.
;;; 
;;; The expression `(subset T s1 s2)` means that
;;;  the set `s1` is a subset of `s2`, i.e. `s1`⊆`s2`.&quot;
;;;   [[T :type] [s1 (set T)] [s2 (set T)]]
;;;   (forall [x T]
;;;     (==&gt; (elem T x s1)
;;;          (elem T x s2))))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(source set/subset-refl)
;; @@
;; ->
;;; (defthm subset-refl
;;;   &quot;The subset relation is reflexive.&quot;
;;;   [[T :type] [s (set T)]]
;;;   (subset T s s))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(source set/subset-trans)
;; @@
;; ->
;;; (defthm subset-trans
;;;   &quot;The subset relation is transitive.&quot;
;;;   [[T :type] [s1 (set T)] [s2 (set T)] [s3 (set T)]]
;;;   (==&gt; (subset T s1 s2)
;;;        (subset T s2 s3)
;;;        (subset T s1 s3)))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(defthm subset-antisym
  "The subset ordering is antisymmetric."
  [[T :type] [s1 (set T)] [s2 (set T)]]
  (==> (subset T s1 s2)
       (subset T s2 s1)
       (seteq T s1 s2)))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  subset-antisym
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>subset-antisym</span>","value":"subset-antisym"}],"value":"[:declared :theorem subset-antisym]"}
;; <=

;; @@
(proof subset-antisym
   :script
   (assume [H1 (subset T s1 s2)
            H2 (subset T s2 s1)]
      (qed ((p/and-intro (subset T s1 s2)
                         (subset T s2 s1)) H1 H2))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>subset-antisym</span>","value":"subset-antisym"}],"value":"[:qed subset-antisym]"}
;; <=

;; **
;;; ## The powerset construction
;;; 
;;; In the predicate-as-set approach to encoding set-theoretic notions in type theory, it is relatively cumbersome to deal with the powerset. The main reason is that the constructor `(set T)` (i.e. `(==> T :type)`) is a kind and not a type itself.
;;; 
;;; If a set of type `(set T)` is represented by a predicate of type `(==> T :type)`, then it seems natural to encode a powerset (i.e. a set of sets) as follows.
;; **

;; @@
(definition powerset
  "The powerset constructor."
  [[T :type]]
  (==> (set T) :type))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>powerset</span>","value":"powerset"}],"value":"[:defined :term powerset]"}
;; <=

;; @@
(definition set-elem
  "Membership for powerset."
  [[T :type] [x (set T)] [X (powerset T)]]
  (X x))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>set-elem</span>","value":"set-elem"}],"value":"[:defined :term set-elem]"}
;; <=

;; **
;;; ## Bounds
;;; 
;;; We translate the notion of lower bound (resp. upper bound) for the subset relation.
;; **

;; @@
(definition subset-lower-bound
  "A lower bound `l` of a powerset `X` in the subset ordering."
  [[T :type] [X (powerset T)] [l (set T)]]
  (forall [x (set T)]
     (==> (set-elem T x X)
          (subset T l x))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>subset-lower-bound</span>","value":"subset-lower-bound"}],"value":"[:defined :term subset-lower-bound]"}
;; <=

;; @@
(definition subset-upper-bound
  "An upper bound `u` of a powerset `X` in the subset ordering."
  [[T :type] [X (powerset T)] [u (set T)]]
  (forall [x (set T)]
     (==> (set-elem T x X)
          (subset T x u))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>subset-upper-bound</span>","value":"subset-upper-bound"}],"value":"[:defined :term subset-upper-bound]"}
;; <=

;; **
;;; The associated notions of greatest lower bound (resp. least upper bound).
;; **

;; @@
(definition subset-glb
  "The least lower bound `l` of a subset `X` in the subset ordering."
  [[T :type] [X (powerset T)] [l (set T)]]
  (and (subset-lower-bound T X l)
       (forall [x (set T)]
          (==> (subset-lower-bound T X x)
               (subset T x l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>subset-glb</span>","value":"subset-glb"}],"value":"[:defined :term subset-glb]"}
;; <=

;; @@
(definition subset-lub
  "The least upper bound `u` of a subset `X` in the subset ordering."
  [[T :type] [X (powerset T)] [u (set T)]]
  (and (subset-upper-bound T X u)
       (forall [x (set T)]
          (==> (subset-upper-bound T X x)
               (subset T u x)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>subset-lub</span>","value":"subset-lub"}],"value":"[:defined :term subset-lub]"}
;; <=

;; @@

;; @@
