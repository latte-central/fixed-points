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
                                          assume have proof try-proof]]
            [latte.quant :as q :refer [exists]]
            [latte.prop :as p :refer [<=> and or not]]
            [latte.equal :as eq :refer [equal]]
            [latte.rel :as rel :refer [rel]]
            [latte-sets.core :as set :refer [set elem
                                             subset seteq emptyset forall-in]]
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
;;; Another example is the set of strings over an alphabet @@\Sigma@@, denoted by @@\Sigma^*@@.
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
;;; ## Closed sets
;; **

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
;;; ## Inductive sets
;; **

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
(defthm inductive-set-lower-bound
  "If `Q` is an `R`-closed set, then the inductive
  set defined on `R` is included in `Q`."
  [[T :type] [R (rules T)] [Q (set T)]]
  (==> (closed-set T R Q)
       (subset T (inductive-set T R) Q)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inductive-set-lower-bound</span>","value":"inductive-set-lower-bound"}],"value":"[:declared :theorem inductive-set-lower-bound]"}
;; <=

;; @@
(proof inductive-set-lower-bound
    :script
    (assume [H (closed-set T R Q)]
       (have a (subset T (inductive-set T R) Q)
           :by ((pset/intersections-lower-bound T (lambda [E (set T)]
                                                        (closed-set T R E)))
                Q H))
       (qed a)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inductive-set-lower-bound</span>","value":"inductive-set-lower-bound"}],"value":"[:qed inductive-set-lower-bound]"}
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
               :by ((inductive-set-lower-bound T R Y) HY))
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
(defthm elem-inductive-set
  "Membership for inductive set"
  [[T :type] [R (rules T)] [X (set T)] [y T]]
  (==> (R X y)
       (subset T X (inductive-set T R))
       (elem T y (inductive-set T R))))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  elem-inductive-set
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>elem-inductive-set</span>","value":"elem-inductive-set"}],"value":"[:declared :theorem elem-inductive-set]"}
;; <=

;; @@
(proof elem-inductive-set
   :script
   (assume [H1 (R X y)
            H2 (subset T X (inductive-set T R))]
      (have <a> (elem T y (inductive-set T R))
            :by ((closed-inductive-set T R) X y H1 H2))
      (qed <a>)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>elem-inductive-set</span>","value":"elem-inductive-set"}],"value":"[:qed elem-inductive-set]"}
;; <=

;; **
;;; ## Rule induction
;; **

;; @@
(defthm inductive-subset-prop
  "If a property `P` has the inductive set defined by
  rules `R` as subset, then each element of the
  inductive set verifies the property."
  [[T :type] [R (rules T)] [P (==> T :type)]]
  (==> (subset T (inductive-set T R) P)
       (forall [x T]
          (==> (elem T x (inductive-set T R))
               (P x)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inductive-subset-prop</span>","value":"inductive-subset-prop"}],"value":"[:declared :theorem inductive-subset-prop]"}
;; <=

;; @@
(proof inductive-subset-prop
   :script
   (assume [HP (subset T (inductive-set T R) P)]
     (assume [x T
              Hx (elem T x (inductive-set T R))]
        (have a (P x) :by (HP x Hx))
        (have b (forall [x T]
                   (==> (elem T x (inductive-set T R))
                        (P x))) :discharge [x Hx a]))
      (qed b)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inductive-subset-prop</span>","value":"inductive-subset-prop"}],"value":"[:qed inductive-subset-prop]"}
;; <=

;; @@
(defthm inductive-closed-prop
  "If a property `P` is `R`-closed, then each element of the
  inductive set verifies the property."
  [[T :type] [R (rules T)] [P (==> T :type)]]
  (==> (closed-set T R P)
       (forall [x T]
          (==> (elem T x (inductive-set T R))
               (P x)))))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  inductive-closed-prop
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inductive-closed-prop</span>","value":"inductive-closed-prop"}],"value":"[:declared :theorem inductive-closed-prop]"}
;; <=

;; @@
(proof inductive-closed-prop
   :script
   (assume [H (closed-set T R P)]
       (have a (subset T (inductive-set T R) P)
             :by ((inductive-set-lower-bound T R P) H))
       (qed a)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inductive-closed-prop</span>","value":"inductive-closed-prop"}],"value":"[:qed inductive-closed-prop]"}
;; <=

;; @@
(defthm rule-induction
  "Rule induction for property `P` about
  inductive rules `R`."
  [[T :type] [R (rules T)] [P (==> T :type)]]
  (==> (forall [X (set T)]
          (forall [y T]
             (==> (R X y)
                  (forall [x T]
                     (==> (elem T x X) 
                          (P x)))
                  (P y))))
       (forall [x T]
          (==> (elem T x (inductive-set T R))
               (P x)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>rule-induction</span>","value":"rule-induction"}],"value":"[:declared :theorem rule-induction]"}
;; <=

;; @@
(proof rule-induction :term (inductive-closed-prop T R P))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>rule-induction</span>","value":"rule-induction"}],"value":"[:qed rule-induction]"}
;; <=

;; **
;;; ## Example: the inductive set of natural numbers
;; **

;; @@
(defaxiom nat
  ""
  []
  :type)
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:axiom</span>","value":":axiom"},{"type":"html","content":"<span class='clj-symbol'>nat</span>","value":"nat"}],"value":"[:declared :axiom nat]"}
;; <=

;; @@
(defaxiom zero
  ""
  []
  nat)
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:axiom</span>","value":":axiom"},{"type":"html","content":"<span class='clj-symbol'>zero</span>","value":"zero"}],"value":"[:declared :axiom zero]"}
;; <=

;; @@
(defaxiom succ
  ""
  []
  (==> nat nat))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:axiom</span>","value":":axiom"},{"type":"html","content":"<span class='clj-symbol'>succ</span>","value":"succ"}],"value":"[:declared :axiom succ]"}
;; <=

;; @@
(definition nat-rules
  "The inductive rules for the natural numbers."
  []
  (lambda [X (set nat)]
     (lambda [y nat]
        (or (and (seteq nat X (emptyset nat))
                 (equal nat y zero))
            (forall [n nat]
                (and (seteq nat X (lambda [k nat] (equal nat k n)))
                     (equal nat y (succ n))))))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>nat-rules</span>","value":"nat-rules"}],"value":"[:defined :term nat-rules]"}
;; <=

;; @@
(definition nat-set
  "The inductive set of natural numbers."
  []
  (inductive-set nat nat-rules))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>nat-set</span>","value":"nat-set"}],"value":"[:defined :term nat-set]"}
;; <=

;; @@
(defthm elem-seteq-equal
  "membership property of a singleton set"
  [[T :type] [s (set T)] [x T]]
  (==> (seteq T s (lambda [y T] (equal  T y x)))
       (elem T x s)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>elem-seteq-equal</span>","value":"elem-seteq-equal"}],"value":"[:declared :theorem elem-seteq-equal]"}
;; <=

;; @@
(proof elem-seteq-equal
   :script
   (assume [H1 (seteq T s (lambda [y T] (equal T y x)))]
      (have <a> (elem T x (lambda [y T] (equal T y x)))
            :by (eq/eq-refl T x))
      (have <b> (elem T x s) :by ((p/%and-elim-right H1) x <a>))
      (qed <b>)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>elem-seteq-equal</span>","value":"elem-seteq-equal"}],"value":"[:qed elem-seteq-equal]"}
;; <=

;; @@
(defthm nat-rule-induction
  "Rule induction for property `P` about
  natural numbers."
  [[P (==> T :type)]]
  (==> (forall [N (set nat)]
          (forall [n nat]
             (==> (R N n)
                  (forall [k nat]
                     (==> (elem nat k N) 
                          (P k)))
                  (P n))))
       (forall [n nat]
          (==> (elem nat n nat-set)
               (P n)))))
;; @@

;; @@
(defthm nat-induction
  "Rule induction for property `P` about
  natural numbers."
  [[P (==> nat :type)]]
  (==> (P zero)
       (forall-in [k nat nat-set]
          (==> (P k) (P (succ k))))
       (forall-in [n nat nat-set] (P n))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>nat-induction</span>","value":"nat-induction"}],"value":"[:declared :theorem nat-induction]"}
;; <=

;; @@
(try-proof nat-induction
    :script
    (assume [Hz (P zero)
             Hs (forall-in [k nat nat-set]
                   (==> (P k) (P (succ k))))]
       (assume [n nat
                Hn (elem nat n nat-set)]
          (assume [N (set nat)
                   HNn (nat-rules N n)]
             (have <a> (==> (==> (and (seteq nat N (emptyset nat))
                                      (equal nat n zero))
                                 (P n))
                            (==> (forall [m nat]
                                   (and (seteq nat N (lambda [k nat] (equal nat k m)))
                                        (equal nat n (succ m))))
                                 (P n))
                            (P n)) :by ((p/or-elim (and (seteq nat N (emptyset nat))
                                                        (equal nat n zero))
                                                   (forall [m nat]
                                                      (and (seteq nat N (lambda [k nat] (equal nat k m)))
                                                           (equal nat n (succ m)))))
                                        HNn (P n)))))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:ko</span>","value":":ko"},{"type":"list-like","open":"<span class='clj-map'>{</span>","close":"<span class='clj-map'>}</span>","separator":", ","items":[{"type":"list-like","open":"","close":"","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:proof-incomplete</span>","value":":proof-incomplete"},{"type":"html","content":"<span class='clj-symbol'>nat-induction</span>","value":"nat-induction"}],"value":"[:proof-incomplete nat-induction]"}],"value":"{:proof-incomplete nat-induction}"}],"value":"[:ko {:proof-incomplete nat-induction}]"}
;; <=

;; @@

;; @@
