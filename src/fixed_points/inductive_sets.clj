;; gorilla-repl.fileformat = 1

;; **
;;; # Inductive sets
;;; 
;;; In this document we discuss one possible formalization of *inductive sets*. We do not directly used the fixed point theorems but we see how inductively-defined sets can be formalized using a relational approach.
;; **

;; @@
(ns fixed-points.inductive-sets
  (:refer-clojure :exclude [and or not set])

  (:require [latte.core :as latte :refer [definition defthm defaxiom
                                          forall lambda ==>
                                          assume have proof lambda]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]
            [latte.rel :as rel :refer [rel]]
            [latte-sets.core :as set :refer [set elem
                                             subset seteq]]
            [latte-sets.powerset :as pset :refer [powerset intersections]]))
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
;;; ## Rules
;;; 
;;; Inductively defined sets are often described using logical rules.
;;; For example, the set of natural number can be described as the *least* set satisfying the rules below.
;;; 
;;; $$\dfrac{}{0\in \mathbb{N}}  \quad \forall n. \dfrac{\\{n\\}\subseteq\mathbb{N}}{succ(n)\in \mathbb{N}}$$
;;; 
;;; Another example is the set of strings over an alphabet @@\Sigma@@, denoted by $\Sigma^*$.
;;; 
;;; $$\dfrac{}{\epsilon\in \Sigma^\*}  \quad \forall x. \forall a. a\in\Sigma \implies \dfrac{\\{x\\}\subseteq\Sigma^\*}{ax \in \Sigma^*}$$
;;; 
;;; Given a type @@T@@, a rule instance on @@T@@ is of the form @@(X,y)@@ with @@X@@ a set of @@T@@-elements and @@y@@ a @@T@@-element. The intended meaning is that if @@X@@ is a subset of the inductive set, then we can deduce that @@y@@ is *also* an element.   Hence, a rule-based definition is a relation from powersets to sets.
;; **

;; @@
(definition rules
  "The constructor for rule sets."
  [[T :type]]
  (==> (set T) T :type))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>rules</span>","value":"rules"}],"value":"[:defined :term rules]"}
;; <=

;; **
;;; We next introduce the notion of a @@R@@-closed set, with @@R@@ a rule set.
;; **

;; @@
(definition closed-set
  "The set `E` is `R`-closed."
  [[T :type] [R (rules T)] [E (set T)]]
  (forall [X (set T)]
      (forall [y T]
        (==> (R X y)
             (subset T X E)
             (elem T y E)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>closed-set</span>","value":"closed-set"}],"value":"[:defined :term closed-set]"}
;; <=

;; **
;;; We can now provide the set inductively defined on a rule set @@R@@ as the intersection of all @@R@@-closed sets.
;; **

;; @@
(definition inductive-set
  "The set inductively defined on `R`."
  [[T :type] [R (rules T)]]
  (intersections T (lambda [E (set T)]
                       (closed-set T R E))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>inductive-set</span>","value":"inductive-set"}],"value":"[:defined :term inductive-set]"}
;; <=

;; @@
(defthm closed-set-lower-bound
  "If `Q` is an `R`-closed set, then the inductive
  set defined on `R` is included in `Q`."
  [[T :type] [R (rules T)] [Q (set T)]]
  (==> (closed-set T R Q)
       (subset T (inductive-set T R) Q)))
;; @@

;; @@
(proof closed-set-lower-bound
    :script
    (assume [H (closed-set T R Q)]
       (have a (subset T (inductive-set T R) Q)
           :by ((pset/intersections-lower-bound T (lambda [E (set T)]
                                                        (closed-set T R E)))
                Q H))
       (qed a)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>closed-set-lower-bound</span>","value":"closed-set-lower-bound"}],"value":"[:qed closed-set-lower-bound]"}
;; <=

;; **
;;; A property of this set is that it is itself @@R@@-closed.
;; **

;; @@
(defthm closed-inductive-set
  "The set inductively defined on `R` is `R`-closed."
  [[T :type] [R (rules T)]]
  (closed-set T R (inductive-set T R)))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  closed-inductive-set
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>closed-inductive-set</span>","value":"closed-inductive-set"}],"value":"[:declared :theorem closed-inductive-set]"}
;; <=

;; @@
(proof closed-inductive-set
   :script
   (assume [X (set T)
            y T
            H1 (R X y)
            H2 (subset T X (inductive-set T R))]
      (assume [Y (set T)
               HY (closed-set T R Y)]
         (have a (subset T (inductive-set T R) Y)
               :by ((closed-set-lower-bound T R Y) HY))
         (have b (subset T X Y)
               :by ((set/subset-trans T X (inductive-set T R) Y)
                    H2 a))
         (have c (elem T y Y) :by (HY X y H1 b))
         (have d (forall [Y (set T)]
                    (==> (closed-set T R Y)
                         (elem T y Y)))
               :discharge [Y HY c]))
       (qed d)))      
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>closed-inductive-set</span>","value":"closed-inductive-set"}],"value":"[:qed closed-inductive-set]"}
;; <=

;; @@
(defthm inductive-prop
  ""
  [[T :type] [R (rules T)] [P (==> T :type)]]
  (==> (subset T (inductive-set T R)
               (lambda [x T]
                  (and (elem T x (inductive-set T R))
                       (P x))))
       (forall [x T]
          (==> (elem T x (inductive-set T R))
               (P x)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inductive-prop</span>","value":"inductive-prop"}],"value":"[:declared :theorem inductive-prop]"}
;; <=

;; @@
(proof inductive-prop
   :script
   )
;; @@

;; @@
(defthm rule-induction
  "The principle of rule induction."
  [[T :type] [R (rules T)] [P (==> T :type)]]
  (==> (forall [X (set T)]
           (forall [y T]
               (==> (R X y)
                    (forall [x T]
                       (==> (elem T x X)
                            (and (elem T x (inductive-set T R))
                                 (P x))))
                    (P y))))
       (forall [x T]
          (==> (elem T x (inductive-set T R))
               (P x)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>rule-induction</span>","value":"rule-induction"}],"value":"[:declared :theorem rule-induction]"}
;; <=

;; @@

;; @@
