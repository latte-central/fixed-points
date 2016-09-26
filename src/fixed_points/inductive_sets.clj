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
;; ->
;;; [Warning] redefinition as term:  rules
;;; 
;; <-
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
;; ->
;;; [Warning] redefinition as term:  closed-set
;;; 
;; <-
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
;; ->
;;; [Warning] redefinition as term:  inductive-set
;;; 
;; <-
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
;; ->
;;; [Warning] redefinition as theorem:  inductive-set-lower-bound
;;; 
;; <-
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
;; ->
;;; [Warning] redefinition as theorem:  closed-inductive-set
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>closed-inductive-set</span>","value":"closed-inductive-set"}],"value":"[:declared :theorem closed-inductive-set]"}
;; <=

;; **
;;; This means :
;;; 
;;; ```clojure
;;; (forall [X (set T)]
;;;       (forall [y T]
;;;         (==> (R X y)
;;;              (subset T X (inductive-set T R))
;;;              (elem T y (inductive-set T R))))))
;;; ```
;;; 
;;; The proof is not difficult.
;; **

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
(defthm rule-induction
  "If a property `P` is `R`-closed, then each element of the
  inductive set verifies the property."
  [[T :type] [R (rules T)] [P (==> T :type)]]
  (==> (closed-set T R P)
       (forall [x T]
          (==> (elem T x (inductive-set T R))
               (P x)))))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  rule-induction
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>rule-induction</span>","value":"rule-induction"}],"value":"[:declared :theorem rule-induction]"}
;; <=

;; @@
(proof rule-induction
   :script
   (assume [H (closed-set T R P)]
       (have a (subset T (inductive-set T R) P)
             :by ((inductive-set-lower-bound T R P) H))
       (qed a)))
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
;; ->
;;; [Warning] redefinition as axiom:  nat
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:axiom</span>","value":":axiom"},{"type":"html","content":"<span class='clj-symbol'>nat</span>","value":"nat"}],"value":"[:declared :axiom nat]"}
;; <=

;; @@
(defaxiom zero
  ""
  []
  nat)
;; @@
;; ->
;;; [Warning] redefinition as axiom:  zero
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:axiom</span>","value":":axiom"},{"type":"html","content":"<span class='clj-symbol'>zero</span>","value":"zero"}],"value":"[:declared :axiom zero]"}
;; <=

;; @@
(defaxiom succ
  ""
  []
  (==> nat nat))
;; @@
;; ->
;;; [Warning] redefinition as axiom:  succ
;;; 
;; <-
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
;; ->
;;; [Warning] redefinition as term:  nat-rules
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>nat-rules</span>","value":"nat-rules"}],"value":"[:defined :term nat-rules]"}
;; <=

;; @@
(definition nat-set
  "The inductive set of natural numbers."
  []
  (inductive-set nat nat-rules))
;; @@
;; ->
;;; [Warning] redefinition as term:  nat-set
;;; 
;; <-
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
;; ->
;;; [Warning] redefinition as theorem:  elem-seteq-equal
;;; 
;; <-
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
(defthm nat-induct-closed
  "Rule induction for property `P` about
  natural numbers."
  [[P (==> nat :type)]]
  (==> (P zero)
       (forall [k nat] (==> (P k) (P (succ k))))
       (closed-set nat nat-rules P)))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  nat-induct-closed
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>nat-induct-closed</span>","value":"nat-induct-closed"}],"value":"[:declared :theorem nat-induct-closed]"}
;; <=

;; @@
(proof nat-induct-closed
    :script
  (assume [Hz (P zero)
           Hs (forall [k nat] (==> (P k) (P (succ k))))]
    (assume [N (set nat)
             n nat
             HNn (nat-rules N n)
             Hsub (subset nat N P)]
      "We proceed by case analysis on nat-rules"
      "The first case if if n=zero"
      (assume [Hzero (and (seteq nat N (emptyset nat))
                          (equal nat n zero))]
        (have <a1> (P n)
              :by ((eq/eq-subst nat P zero n)
                   ((eq/eq-sym nat n zero) (p/%and-elim-right Hzero))
                   Hz))
        (have <a> _ :discharge [Hzero <a1>]))
      "The second case if if n=(succ m) for some m."
      (assume [m nat
               Hm (and (seteq nat N (lambda [k nat] (equal nat k m)))
                       (equal nat n (succ m)))]
        (have <b1> (elem nat m N) 
              :by ((elem-seteq-equal nat N m) 
                   (p/%and-elim-left Hm)))
        (have <b2> (P m) :by (Hsub m <b1>))
        (have <b3> (P (succ m)) :by (Hs m <b2>))
        (have <b4> (P n) :by ((eq/eq-subst nat P (succ m) n)
                              ((eq/eq-sym nat n (succ m)) (p/%and-elim-right Hm))
                              <b3>))
        (have <b5> (forall [m nat]
                     (==> (and (seteq nat N (lambda [k nat] (equal nat k m)))
                               (equal nat n (succ m)))
                          (P n))) :discharge [m Hm <b4>]))
      (assume [H (forall [m nat]
                   (and (seteq nat N (lambda [k nat] (equal nat k m)))
                        (equal nat n (succ m))))]
        (assume [m nat]
          (have <b6> (P n) :by (<b5> m (H m)))
          (have <b7> (==> nat (P n)) :discharge [m <b6>]))
        (have <b8> (P n) :by (<b7> zero))
        (have <b> (==> (forall [m nat]
                         (and (seteq nat N (lambda [k nat] (equal nat k m)))
                              (equal nat n (succ m))))
                       (P n)) :discharge [H <b8>]))
      "Joining the two cases..."
      (have <c> (==> (==> (and (seteq nat N (emptyset nat))
                               (equal nat n zero))
                          (P n))
                     (==> (forall [m nat]
                            (and (seteq nat N (lambda [k nat] (equal nat k m)))
                                 (equal nat n (succ m))))
                          (P n))
                     (P n))
            :by ((p/or-elim (and (seteq nat N (emptyset nat))
                                 (equal nat n zero))
                            (forall [m nat]
                              (and (seteq nat N (lambda [k nat] (equal nat k m)))
                                   (equal nat n (succ m)))))
                 HNn (P n)))
      (have <d> (P n) :by (<c> <a> <b>))
      (have <e> _ :discharge [N n HNn Hsub <d>]))
    (qed <e>)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>nat-induct-closed</span>","value":"nat-induct-closed"}],"value":"[:qed nat-induct-closed]"}
;; <=

;; @@
(defthm nat-induction
  "Rule induction for property `P` about
  natural numbers."
  [[P (==> nat :type)]]
  (==> (P zero)
       (forall [k nat]
          (==> (P k) (P (succ k))))
       (forall-in [n nat nat-set] (P n))))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  nat-induction
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>nat-induction</span>","value":"nat-induction"}],"value":"[:declared :theorem nat-induction]"}
;; <=

;; @@
(proof nat-induction
   :script
   (assume [Hz (P zero)
            Hs (forall [k nat]
                  (==> (P k) (P (succ k))))]
      (have <a> (closed-set nat nat-rules P)
            :by ((nat-induct-closed P) Hz Hs))
      (have <b> (forall-in [n nat nat-set] (P n))
            :by ((rule-induction nat nat-rules P)
                 <a>))
      (qed <b>)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>nat-induction</span>","value":"nat-induction"}],"value":"[:qed nat-induction]"}
;; <=

;; @@
(defthm zero-elem-nat
  "Zero is a natural number."
  []
  (elem nat zero nat-set))
;; @@
;; ->
;;; [Warning] redefinition as theorem:  zero-elem-nat
;;; 
;; <-
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>zero-elem-nat</span>","value":"zero-elem-nat"}],"value":"[:declared :theorem zero-elem-nat]"}
;; <=

;; @@
(proof zero-elem-nat
    :script
  (have <a> (seteq nat (emptyset nat) (emptyset nat))
        :by (set/seteq-refl nat (emptyset nat)))
  (have <b> (equal nat zero zero) :by (eq/eq-refl nat zero))
  (have <c> _ :by (p/%and-intro <a> <b>))
  (have <d> (nat-rules (emptyset nat) zero)
        :by ((p/or-intro-left (and (seteq nat (emptyset nat) (emptyset nat)) (equal nat zero zero))
                              (forall [n nat]
                                (and
                                 (seteq nat (emptyset nat) (lambda [k nat] (equal nat k n)))
                                 (equal nat zero (succ n)))))
             <c>))
  (have <e> (subset nat (emptyset nat) nat-set)
        :by (set/emptyset-subset-lower-bound nat nat-set))
  (have <f> (elem nat zero nat-set)
        :by ((elem-inductive-set nat nat-rules (emptyset nat) zero)
             <d> <e>))
  (qed <f>))
;; @@

;; @@
(defthm succ-elem-nat
  "The successor of a natural number is a natural number."
  [[n nat]]
  (==> (elem nat n nat-set)
       (elem nat (succ n) nat-set)))
;; @@

;; @@
(proof succ-elem-nat
    :script
  (assume [H (elem nat n nat-set)]
    (have <c> (nat-rules (lambda [k nat] (equal nat k n)) (succ n)) 
      )))
;; @@
