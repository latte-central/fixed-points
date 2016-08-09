;; gorilla-repl.fileformat = 1

;; **
;;; # Fixed points in complete lattices
;;; 
;; **

;; @@
(ns fixed-points.complete-lattices
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

;; @@
(use 'clojure.repl)
;; @@
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; **
;;; In this document we provide a formal proof of one of the simplest and perhaps most useful *fixed point theorem*. The formalization is conducted on a computer using the [LaTTe proof assistant](https://github.com/fredokun/LaTTe).
;; **

;; **
;;; ## Ordering relations
;; **

;; **
;;; Our starting points are *ordering relations*. We thus recall the definition of a **relation on a type** `T` below.
;; **

;; @@
(source rel)
;; @@
;; ->
;;; (definition rel
;;;   &quot;The type of relations.&quot;
;;;   [[T :type]]
;;;   (==&gt; T T :type))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; **
;;; Ordering relations are *reflexive* and *transitive*. We recall these properties below.
;; **

;; @@
(source rel/reflexive)
;; @@
;; ->
;;; (definition reflexive
;;;   &quot;A reflexive relation.&quot;
;;;   [[T :type] [R (rel T)]]
;;;   (forall [x T] (R x x)))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(source rel/transitive)
;; @@
;; ->
;;; (definition transitive
;;;   &quot;A transitive relation.&quot;
;;;   [[T :type] [R (rel T)]]
;;;   (forall [x y z T]
;;;     (==&gt; (R x y)
;;;          (R y z)
;;;          (R x z))))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; **
;;; A relation that is both reflexive and transitive is called a **preorder**.
;; **

;; @@
(definition preorder
  "A preorder is a relation `R`` on type `T` that is reflexive and transitive."
  [[T :type] [R (rel T)]]
  (and (rel/reflexive T R)
       (rel/transitive T R)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>preorder</span>","value":"preorder"}],"value":"[:defined :term preorder]"}
;; <=

;; **
;;; To obtain an **order**, also known as a *partially-ordered set* (but this terminology does not fit well in the context of type theory), one has to add **antisymmetry*.
;; **

;; @@
(definition antisymmetric
  "The property of antisymmetry for relation `R` on `T`."
  [[T :type] [R (rel T)]]
  (forall [x y T]
      (==> (R x y)
           (R y x)
           (equal T x y))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>antisymmetric</span>","value":"antisymmetric"}],"value":"[:defined :term antisymmetric]"}
;; <=

;; @@
(definition order
  "An ordering relation `R` on type `T`."
  [[T :type] [R (rel T)]]
  (and (preorder T R)
       (antisymmetric T R)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>order</span>","value":"order"}],"value":"[:defined :term order]"}
;; <=

;; **
;;; An **inverse relation** or an order (resp. preorder) remains an order (resp. preorder).
;; **

;; @@
(definition inverse-rel
  "The inverse relation of `R` on type `T`"
  [[T :type] [R (rel T)]]
  (lambda [x y T]
      (R y x)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>inverse-rel</span>","value":"inverse-rel"}],"value":"[:defined :term inverse-rel]"}
;; <=

;; @@
(defthm inv-refl
  "Inversion preserves reflexivity"
  [[T :type] [R (rel T)]]
  (==> (rel/reflexive T R)
       (rel/reflexive T (inverse-rel T R))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-refl</span>","value":"inv-refl"}],"value":"[:declared :theorem inv-refl]"}
;; <=

;; @@
(proof inv-refl :script
   (assume [H (rel/reflexive T R)
            x T]
      (have R' _ :by (inverse-rel T R))
      (have a (R x x) :by (H x))
      (have b (R' x x) :by a)
      (qed b)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-refl</span>","value":"inv-refl"}],"value":"[:qed inv-refl]"}
;; <=

;; @@
(defthm inv-trans
  "Inversion preserves transitivity."
  [[T :type] [R (rel T)]]
  (==> (rel/transitive T R)
       (rel/transitive T (inverse-rel T R))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-trans</span>","value":"inv-trans"}],"value":"[:declared :theorem inv-trans]"}
;; <=

;; @@
(proof inv-trans :script
   (assume [H (rel/transitive T R)
            x T
            y T
            z T]
      (have R' _ :by (inverse-rel T R))
      (assume [H1 (R' x y)
               H2 (R' y z)]
      	(have a (R z y) :by H2)
      	(have b (R y x) :by H1)
        (have c (R z x) :by ((H z y x) a b))
      	(have d (R' x z) :by c)
        (have e _ :discharge [H1 H2 d]))
        (have f (rel/transitive T (inverse-rel T R)) :discharge [x y z e])
    (qed f)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-trans</span>","value":"inv-trans"}],"value":"[:qed inv-trans]"}
;; <=

;; @@
(defthm inv-preorder
  "Inverse of a preorder is a preorder."
  [[T :type] [R (rel T)]]
  (==> (preorder T R)
       (preorder T (inverse-rel T R))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-preorder</span>","value":"inv-preorder"}],"value":"[:declared :theorem inv-preorder]"}
;; <=

;; @@
(proof inv-preorder :script
    (assume [H (preorder T R)]
        (have a1 (rel/reflexive T R) :by (p/%and-elim-left H))
        (have a (rel/reflexive T (inverse-rel T R)) :by ((inv-refl T R) a1))
        (have b1 (rel/transitive T R) :by (p/%and-elim-right H))
        (have b (rel/transitive T (inverse-rel T R)) :by ((inv-trans T R) b1))
        (qed ((p/and-intro (rel/reflexive T (inverse-rel T R))
                           (rel/transitive T (inverse-rel T R))) a b))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-preorder</span>","value":"inv-preorder"}],"value":"[:qed inv-preorder]"}
;; <=

;; @@
(defthm inv-antisym
  "Inversion preserves antisymmetry."
  [[T :type] [R (rel T)]]
  (==> (antisymmetric T R)
       (antisymmetric T (inverse-rel T R))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-antisym</span>","value":"inv-antisym"}],"value":"[:declared :theorem inv-antisym]"}
;; <=

;; @@
(proof inv-antisym :script
   (assume [H (antisymmetric T R)
            x T
            y T]
      (have R' _ :by (inverse-rel T R))
      (assume [H1 (R' x y)
               H2 (R' y x)]
      	(have a (R x y) :by H2)
      	(have b (R y x) :by H1)
        (have c (equal T x y) :by (H x y a b))
        (have d _ :discharge [x y H1 H2 c]))
        (qed d)))

;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-antisym</span>","value":"inv-antisym"}],"value":"[:qed inv-antisym]"}
;; <=

;; @@
(defthm inv-order
  "Inverse of an order is an order."
  [[T :type] [R (rel T)]]
  (==> (order T R)
       (order T (inverse-rel T R))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-order</span>","value":"inv-order"}],"value":"[:declared :theorem inv-order]"}
;; <=

;; @@
(proof inv-order :script
    (assume [H (order T R)]
        (have a1 (preorder T R) :by (p/%and-elim-left H))
        (have a (preorder T (inverse-rel T R)) :by ((inv-preorder T R) a1))
        (have b1 (antisymmetric T R) :by (p/%and-elim-right H))
        (have b (antisymmetric T (inverse-rel T R)) :by ((inv-antisym T R) b1))
        (qed ((p/and-intro (preorder T (inverse-rel T R))
                           (antisymmetric T (inverse-rel T R))) a b))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-order</span>","value":"inv-order"}],"value":"[:qed inv-order]"}
;; <=

;; **
;;; ## Bounds
;; **

;; **
;;; Lattice properties of ordering relations are based on the notions of **lower bounds** and **upper bounds**.
;; **

;; @@
(definition lower-bound
  "A lower bound `l` of a subset `X` in an order `R` of type `T`."
  [[T :type] [R (rel T)] [X (set T)] [l T]]
  (forall [x T]
     (==> (elem T x X)
          (R l x))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>lower-bound</span>","value":"lower-bound"}],"value":"[:defined :term lower-bound]"}
;; <=

;; @@
(definition upper-bound
  "An upper bound `u` of a subset `X` in an order `R` of type `T`."
  [[T :type] [R (rel T)] [X (set T)] [u T]]
  (forall [x T]
     (==> (elem T x X)
          (R x u))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>upper-bound</span>","value":"upper-bound"}],"value":"[:defined :term upper-bound]"}
;; <=

;; **
;;; Note that the bound `l` (resp. `u`) in `(lower-bound T R X l)` (resp. `(upper-bound T R X u)`) may not be in set `X`, we just state that it is of type `T`. This is to be contrasted with the stronger notion of a **least element** (resp. **greatest element**).
;; **

;; @@
(definition least-element
  "A least element `l` of a subset `X` in an order `R` of type `T`."
  [[T :type] [R (rel T)] [X (set T)] [l T]]
  (and (elem T l X)
       (lower-bound T R X l)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>least-element</span>","value":"least-element"}],"value":"[:defined :term least-element]"}
;; <=

;; @@
(definition greatest-element
  "A greatest element `u` of a subset `X` in an order `R` of type `T`."
  [[T :type] [R (rel T)] [X (set T)] [u T]]
  (and (elem T u X)
       (upper-bound T R X u)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>greatest-element</span>","value":"greatest-element"}],"value":"[:defined :term greatest-element]"}
;; <=

;; **
;;; A lower bound for an ordering relation `R` becomes an upper bound for the inverse of `R`, and *vice versa*. We will often take advantage for *dualizing* the proofs about orders.
;; **

;; @@
(defthm inv-lower-bound
  "The lower bound of a relation `R` becomes an upper bound
  in the inverse relation."
  [[T :type] [R (rel T)]]
  (forall [X (set T)]
     (forall [l T]
        (==> (lower-bound T R X l)
             (upper-bound T (inverse-rel T R) X l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-lower-bound</span>","value":"inv-lower-bound"}],"value":"[:declared :theorem inv-lower-bound]"}
;; <=

;; @@
(proof inv-lower-bound :script
   (assume [X (set T)
            l T
            H (lower-bound T R X l)]
      (have R' _ :by (inverse-rel T R))
      (assume [x T
               Hx (elem T x X)]
        (have a (R l x) :by (H x Hx))
        (have b (R' x l) :by a)
        (have c (upper-bound T R' X l) :discharge [x Hx b]))
      (have d _ :discharge [H c])
      (qed d)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-lower-bound</span>","value":"inv-lower-bound"}],"value":"[:qed inv-lower-bound]"}
;; <=

;; **
;;; And of course, this works the other way around.
;; **

;; @@
(defthm inv-upper-bound
  "The upper bound of a relation `R` becomes a lower bound
  in the inverse relation."
  [[T :type] [R (rel T)]]
  (forall [X (set T)]
     (forall [u T]
        (==> (upper-bound T R X u)
             (lower-bound T (inverse-rel T R) X u)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-upper-bound</span>","value":"inv-upper-bound"}],"value":"[:declared :theorem inv-upper-bound]"}
;; <=

;; @@
(proof inv-upper-bound :script
   (assume [X (set T)
            u T
            H (upper-bound T R X u)]
      (have R' _ :by (inverse-rel T R))
      (assume [x T
               Hx (elem T x X)]
        (have a (R x u) :by (H x Hx))
        (have b (R' u x) :by a)
        (have c (lower-bound T R' X u) :discharge [x Hx b]))
      (have d _ :discharge [H c])
      (qed d)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-upper-bound</span>","value":"inv-upper-bound"}],"value":"[:qed inv-upper-bound]"}
;; <=

;; **
;;; The similarity in the two last proofs show that many theorems can be obtained (and then demonstrated) by inverting the lower and upper notions (and derived concepts, see below) together with inverting the relation.
;;; 
;;; Among the most important definitions are those of the **greatest lower bound** (a.k.a. `glb`) and **least upper bound** (a.k.a. `lub`).
;; **

;; @@
(definition glb
  "The greatest lower bound of a subset `X` in an order `R` of type `T`."
  [[T :type] [R (rel T)] [X (set T)] [l T]]
  (and (lower-bound T R X l)
       (forall [x T]
          (==> (lower-bound T R X x)
               (R x l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>glb</span>","value":"glb"}],"value":"[:defined :term glb]"}
;; <=

;; @@
(definition lub
  "The least upper bound of a subset `X` in an order `R` of type `T`."
  [[T :type] [R (rel T)] [X (set T)] [l T]]
  (and (upper-bound T R X l)
       (forall [x T]
          (==> (upper-bound T R X x)
               (R l x)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>lub</span>","value":"lub"}],"value":"[:defined :term lub]"}
;; <=

;; **
;;; The `glb` and `lub` are dual concepts.
;; **

;; @@
(defthm inv-glb
  "The inverse of a `glb` is a `lub`."
  [[T :type] [R (rel T)]]
  (forall [X (set T)]
      (forall [l T]
         (==> (glb T R X l)
              (lub T (inverse-rel T R) X l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-glb</span>","value":"inv-glb"}],"value":"[:declared :theorem inv-glb]"}
;; <=

;; @@
(proof inv-glb :script
   "First let's state the main hypotheses."
   (assume [X (set T)
            l T
            Hl (glb T R X l)]
      "From now on the inverse will be noted `R'`."
      (have R' _ :by (inverse-rel T R))
      "A `glb` is a lower bound..."
      (have a1 (lower-bound T R X l) :by (p/%and-elim-left Hl))
      "... and thus is is an upper bound for the inverse
       (according to [[inv-lower-bound]])."
      (have a (upper-bound T R' X l) :by ((inv-lower-bound T R) X l a1))
      "Now let's assume we have `x` an upper bound in `R'`."
      (assume [x T
               Hx (upper-bound T R' X x)]
         "We trivially have that `l` is lower than `x` in `R'`
          (since it is greated in `R`)."
         (have b1 (R' l x) :by ((p/%and-elim-right Hl) x Hx))
         "Thus we have the right part of the conjunction in [[lub]]."
         (have b _ :discharge [x Hx b1]))
      "This is enough to conclude."
      (have c _ :by ((p/and-intro (upper-bound T R' X l)
                                  (forall [x T]
                                     (==> (upper-bound T R' X x)
                                          (R' l x)))) a b))
      (qed c)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-glb</span>","value":"inv-glb"}],"value":"[:qed inv-glb]"}
;; <=

;; @@
(defthm inv-lub
  "The inverse of a `lub` is a `glb`."
  [[T :type] [R (rel T)]]
  (forall [X (set T)]
      (forall [u T]
         (==> (lub T R X u)
              (glb T (inverse-rel T R) X u)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-lub</span>","value":"inv-lub"}],"value":"[:declared :theorem inv-lub]"}
;; <=

;; @@
(proof inv-lub :script
   (assume [X (set T)
            u T
            Hu (lub T R X u)]
      (have R' _ :by (inverse-rel T R))
      (have a1 (upper-bound T R X u) :by (p/%and-elim-left Hu))
      (have a (lower-bound T R' X u) :by ((inv-upper-bound T R) X u a1))
      (assume [x T
               Hx (lower-bound T R' X x)]
         (have b1 (R' x u) :by ((p/%and-elim-right Hu) x Hx))
         (have b _ :discharge [x Hx b1]))
      (have c _ :by ((p/and-intro (lower-bound T R' X u)
                                  (forall [x T]
                                     (==> (lower-bound T R' X x)
                                          (R' x u)))) a b))
      (qed c)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>inv-lub</span>","value":"inv-lub"}],"value":"[:qed inv-lub]"}
;; <=

;; **
;;; An important property of the `lub` and `glb` is that if they exist, then they are unique. The only constraint is that of antisymmetry.
;; **

;; @@
(defthm glb-single
  "Singleness of greateast lower bounds."
  [[T :type] [R (rel T)] [X (set T)]]
  (==> (antisymmetric T R)
       (q/single T (lambda [l T] (glb T R X l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>glb-single</span>","value":"glb-single"}],"value":"[:declared :theorem glb-single]"}
;; <=

;; **
;;; Let's remind the definition of "begin the single...".
;; **

;; @@
(source q/single)
;; @@
;; ->
;;; (definition single
;;;   &quot;The constraint that \&quot;there exists at most\&quot;...&quot;
;;;   [[T :type] [P (==&gt; T :type)]]
;;;   (forall [x y T]
;;;     (==&gt; (P x)
;;;          (P y)
;;;          (equal T x y))))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(proof glb-single :script
   (assume [H (antisymmetric T R)]
      "We suppose two glb's"
      (assume [l1 T
               l2 T
               H1 (glb T R X l1)
               H2 (glb T R X l2)]
      "By definition `l1` and `l2` *are* lower bounds."
      (have a (lower-bound T R X l1) :by (p/%and-elim-left H1))
      (have b (lower-bound T R X l2) :by (p/%and-elim-left H2))
      "Now let's apply the *greatest* constraints."
      "First, `l1` is greater than `l2`."
      (have c (R l2 l1) :by ((p/%and-elim-right H1) l2 b))
      "Second, `l2` is greater than `l1`."
      (have d (R l1 l2) :by ((p/%and-elim-right H2) l1 a))
      "Thus, by antisymmetry (our hypothesis `H`) `l1` and `l2` must be equal."
      (have e (equal T l1 l2) :by (H l1 l2 d c))
      "And this is enough to conclude."
      (have f _ :discharge [l1 l2 H1 H2 e]))
    (qed f)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>glb-single</span>","value":"glb-single"}],"value":"[:qed glb-single]"}
;; <=

;; @@
(defthm glb-unique
  "Unicity of greatest lower bounds."
  [[T :type] [R (rel T)] [X (set T)]]
  (==> (antisymmetric T R)
       (exists [l T] (glb T R X l))
       (q/unique T (lambda [l T] (glb T R X l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>glb-unique</span>","value":"glb-unique"}],"value":"[:declared :theorem glb-unique]"}
;; <=

;; **
;;; Unicity is existence together with "singleness".
;; **

;; @@
(source q/unique)
;; @@
;; ->
;;; (definition unique
;;;   &quot;The constraint that \&quot;there exists a unique\&quot; ...&quot;
;;;   [[T :type] [P (==&gt; T :type)]]
;;;   (and (ex T P)
;;;        (single T P)))
;;; 
;; <-
;; =>
;;; {"type":"html","content":"<span class='clj-nil'>nil</span>","value":"nil"}
;; <=

;; @@
(proof glb-unique :script
  "The hypotheses are antisymmetry and existence."
  (assume [H1 (antisymmetric T R)
           H2 (exists [l T] (glb T R X l))]
     "The first step is to get singleness by `gln-single`."
     (have a (q/single T (lambda [l T] (glb T R X l)))
           :by ((glb-single T R X) H1))
     "And then conclude by the conjunction with existence (hypothesis `H2`)."
     (qed ((p/and-intro (exists [l T] (glb T R X l))
                        (q/single T (lambda [l T] (glb T R X l)))) H2 a))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>glb-unique</span>","value":"glb-unique"}],"value":"[:qed glb-unique]"}
;; <=

;; **
;;; For the least upper bounds let's exploit the duality reasoning in the *singleness* proof.
;; **

;; @@
(defthm lub-single
  "Singleness of least upper bounds."
  [[T :type] [R (rel T)] [X (set T)]]
  (==> (antisymmetric T R)
       (q/single T (lambda [u T] (lub T R X u)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>lub-single</span>","value":"lub-single"}],"value":"[:declared :theorem lub-single]"}
;; <=

;; @@
(proof lub-single :script
   (assume [H (antisymmetric T R)]
      (have R' _ :by (inverse-rel T R))
      (have H' (antisymmetric T R') :by ((inv-antisym T R) H))
      (have a (q/single T (lambda [u T] (glb T R' X u)))
            :by ((glb-single T R' X) H'))
      (assume [u1 T
               u2 T
               Hu1 (lub T R X u1)
               Hu2 (lub T R X u2)]
         (have b (glb T R' X u1) :by ((inv-lub T R) X u1 Hu1))
         (have c (glb T R' X u2) :by ((inv-lub T R) X u2 Hu2))
         (have d (equal T u1 u2) :by (a u1 u2 b c))
         (have e (q/single T (lambda [u T] (lub T R X u)))
               :discharge [u1 u2 Hu1 Hu2 d]))
       (qed e)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>lub-single</span>","value":"lub-single"}],"value":"[:qed lub-single]"}
;; <=

;; @@
(defthm lub-unique
  "Unicity of least upper bounds."
  [[T :type] [R (rel T)] [X (set T)]]
  (==> (antisymmetric T R)
       (exists [u T] (lub T R X u))
       (q/unique T (lambda [u T] (lub T R X u)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>lub-unique</span>","value":"lub-unique"}],"value":"[:declared :theorem lub-unique]"}
;; <=

;; **
;;; For unicity it's quick enough to go the direct way.
;; **

;; @@
(proof lub-unique :script
  (assume [H1 (antisymmetric T R)
           H2 (exists [u T] (lub T R X u))]
     (have a (q/single T (lambda [u T] (lub T R X u)))
           :by ((lub-single T R X) H1))
     (qed ((p/and-intro (exists [u T] (lub T R X u))
                        (q/single T (lambda [u T] (lub T R X u)))) H2 a))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>lub-unique</span>","value":"lub-unique"}],"value":"[:qed lub-unique]"}
;; <=

;; **
;;; TODO :
;;; 
;;;   - bottom and top
;;; 
;;; Now that we developed our understanding (and formalization) of *bounds* we can proceed to the next step in the construction.
;; **

;; **
;;; ## Complete lattices
;;; 
;;; The **complete lattices** are particularly well-behaved ordering relation wrt. the least upper and greatest lower bounds. All their subsets have `glb`'s and `lub`'s. However, as we'll see, it is enough to have "only" `glb`'s or `lub`'s for the definition to hold. Because the least fixed points are somewhat more common in practice we take the `glb` road (but this is somewhat an arbitrary choice, as we will make clear later on).
;; **

;; @@
(definition complete-lattice
  "The definition of a relation `R` on `T` being a complete lattice."
  [[T :type] [R (rel T)]]
  (and (order T R)
       (forall [X (set T)]
          (exists [l T] (glb T R X l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:defined</span>","value":":defined"},{"type":"html","content":"<span class='clj-keyword'>:term</span>","value":":term"},{"type":"html","content":"<span class='clj-symbol'>complete-lattice</span>","value":"complete-lattice"}],"value":"[:defined :term complete-lattice]"}
;; <=

;; **
;;; Let's check that going the `lub` road is equivalent. The following theorem is central, and its proof is relatively non-trivial.
;; **

;; @@
(defthm all-glb-all-lub
  "Having all glb's implies having all lub's."
  [[T :type] [R (rel T)]]
  (==> (antisymmetric T R)
       (forall [X (set T)]
         (exists [l T] (glb T R X l)))
       (forall [X (set T)]
         (exists [u T] (lub T R X u)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>all-glb-all-lub</span>","value":"all-glb-all-lub"}],"value":"[:declared :theorem all-glb-all-lub]"}
;; <=

;; @@
(proof all-glb-all-lub :script
  "First we introduce our two asumptions."
  (assume [H1 (antisymmetric T R)
           H2 (forall [X (set T)]
                (exists [l T] (glb T R X l)))]
    "Now let's assume an arbitrary set `X`."
    (assume [X (set T)]
      "We define `Y` the set of upper bounds of `X`."
      (have Y _ :by (lambda [u T] (upper-bound T R X u)))
      "By hypothesis there is a unique greatest lower bound for `Y`."
      (have <a> (exists [l T] (glb T R Y l)) :by (H2 Y))
      (have glbY-unique _ :by ((glb-unique T R Y) H1 <a>))
      "Let's call this `glbY`."
      (have glbY T :by (q/the T (lambda [l T] (glb T R Y l)) glbY-unique))
      "And we keep the fact that it is indeed *the* greatest lower bound."
      (have <b> (glb T R Y glbY) :by (q/the-prop T (lambda [l T] (glb T R Y l)) glbY-unique))

      "Our objective now is to show that `glbY` is *also* an upper bound for the set `X`."
      "For this we assume an arbitrary element `x` of the set `X`."
      (assume [x T
               Hx (elem T x X)]
        
        "In the first step we'll show that `x` is a lower bound for `Y`."
        (assume [y T
                 Hy (elem T y Y)]
          (have <c1> (upper-bound T R X y) :by Hy)
          (have <c2> (R x y) :by (<c1> x Hx))
          (have <c> (lower-bound T R Y x) :discharge [y Hy <c2>]))

        "Hence since `glbY` is *greatest* we can show that `(R x glbY)`."
        (have <d1> (forall [z T]
                     (==> (lower-bound T R Y z)
                          (R z glbY))) :by (p/%and-elim-right <b>))
        
        (have <d2> (==> (lower-bound T R Y x)
                        (R x glbY)) :by (<d1> x))
        
        (have <d3> (R x glbY) :by (<d2> <c>))

        "Thus `glbY` is an upper bound for `X`."
        (have <d> (upper-bound T R X glbY) :discharge [x Hx <d3>]))
      
      "The second step consists in showing that `glbY` is the *least* upper bound."
      (assume [x T
               Hx (upper-bound T R X x)]

        "Taking an arbitrary upper bound `x`, we can show `(R glbY x)` since
as a `glbY` is a lower bound for `Y` and the assumed `x` is by hypothesis a member of `Y`. "
        
        (have <e1> (elem T x Y) :by Hx)
        (have <e2> (lower-bound T R Y glbY) :by (p/%and-elim-left <b>))
        (have <e3> (R glbY x) :by (<e2> x <e1>))
        (have <e> (forall [x T]
                    (==> (upper-bound T R X x)
                         (R glbY x))) :discharge [x Hx <e3>]))
      
      "Hence we have our main result which is that `glbY` is a `lub` for `X`."
      (have <h> (lub T R X glbY) :by ((p/and-intro (upper-bound T R X glbY)
                                                   (forall [x T]
                                                     (==> (upper-bound T R X x)
                                                          (R glbY x)))) <d> <e>))

      "Hence we've just shown that there exists a lub for `X`, namely `glbY`."
      (have <i> (exists [l T] (lub T R X l))
            :by ((q/ex-intro T (lambda [l T] (lub T R X l)) glbY) <h>))

      (qed <i>))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>all-glb-all-lub</span>","value":"all-glb-all-lub"}],"value":"[:qed all-glb-all-lub]"}
;; <=

;; **
;;; From this we can derive a few interesting properties. First, a corrolary of the previous theorem is that a complete lattice has also all lub's.
;; **

;; @@
(defthm complete-lattice-all-lub
  "A complete lattice have all lub's"
  [[T :type] [R (rel T)]]
  (==> (complete-lattice T R)
       (forall [X (set T)]
            (exists [u T] (lub T R X u)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>complete-lattice-all-lub</span>","value":"complete-lattice-all-lub"}],"value":"[:declared :theorem complete-lattice-all-lub]"}
;; <=

;; @@
(proof complete-lattice-all-lub :script
   (assume [H (complete-lattice T R)]
       (have a (antisymmetric T R) :by (p/%and-elim-right (p/%and-elim-left H)))
       (have b (forall [X (set T)]
                 (exists [l T] (glb T R X l))) :by (p/%and-elim-right H))
       (have c (forall [X (set T)]
                 (exists [u T] (lub T R X u))) :by ((all-glb-all-lub T R) a b))
       (qed c)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>complete-lattice-all-lub</span>","value":"complete-lattice-all-lub"}],"value":"[:qed complete-lattice-all-lub]"}
;; <=

;; **
;;; Conversely, an ordering relation with all lub's is a complete lattice. We could proceed by duality but it is in fact simpler to prooceed "directly".
;; **

;; @@
(defthm all-lub-all-glb
  "Having all lub's implies having all glb's."
  [[T :type] [R (rel T)]]
  (==> (antisymmetric T R)
       (forall [X (set T)]
         (exists [u T] (lub T R X u)))
       (forall [X (set T)]
         (exists [l T] (glb T R X l)))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>all-lub-all-glb</span>","value":"all-lub-all-glb"}],"value":"[:declared :theorem all-lub-all-glb]"}
;; <=

;; @@
(proof all-lub-all-glb :script
  (assume [H1 (antisymmetric T R)
           H2 (forall [X (set T)]
                (exists [u T] (lub T R X u)))]
    (assume [X (set T)]
      (have Y _ :by (lambda [l T] (lower-bound T R X l)))
      (have <a> (exists [u T] (lub T R Y u)) :by (H2 Y))
      (have lubY-unique _ :by ((lub-unique T R Y) H1 <a>))
      (have lubY T :by (q/the T (lambda [u T] (lub T R Y u)) lubY-unique))
      (have <b> (lub T R Y lubY) :by (q/the-prop T (lambda [u T] (lub T R Y u)) lubY-unique))
      (assume [x T
               Hx (elem T x X)]
        (assume [y T
                 Hy (elem T y Y)]
          (have <c1> (lower-bound T R X y) :by Hy)
          (have <c2> (R y x) :by (<c1> x Hx))
          (have <c> (upper-bound T R Y x) :discharge [y Hy <c2>]))
        (have <d1> (forall [z T]
                     (==> (upper-bound T R Y z)
                          (R lubY z))) :by (p/%and-elim-right <b>))
        
        (have <d2> (==> (upper-bound T R Y x)
                        (R lubY x)) :by (<d1> x))
        
        (have <d3> (R lubY x) :by (<d2> <c>))
        (have <d> (lower-bound T R X lubY) :discharge [x Hx <d3>]))
      
      (assume [x T
               Hx (lower-bound T R X x)]
        (have <e1> (elem T x Y) :by Hx)
        (have <e2> (upper-bound T R Y lubY) :by (p/%and-elim-left <b>))
        (have <e3> (R x lubY) :by (<e2> x <e1>))
        (have <e> (forall [x T]
                    (==> (lower-bound T R X x)
                         (R x lubY))) :discharge [x Hx <e3>]))
      (have <h> (glb T R X lubY) :by ((p/and-intro (lower-bound T R X lubY)
                                                   (forall [x T]
                                                     (==> (lower-bound T R X x)
                                                          (R x lubY)))) <d> <e>))

      (have <i> (exists [u T] (glb T R X u))
            :by ((q/ex-intro T (lambda [u T] (glb T R X u)) lubY) <h>))

      (qed <i>))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>all-lub-all-glb</span>","value":"all-lub-all-glb"}],"value":"[:qed all-lub-all-glb]"}
;; <=

;; @@
(defthm complete-lattice-from-lub
  "An order `R` with all lub's is a complete lattice."
  [[T :type] [R (rel T)]]
  (==> (order T R)
       (forall [X (set T)]
           (exists [u T] (lub T R X u)))
       (complete-lattice T R)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>complete-lattice-from-lub</span>","value":"complete-lattice-from-lub"}],"value":"[:declared :theorem complete-lattice-from-lub]"}
;; <=

;; @@
(proof complete-lattice-from-lub :script
   (assume [H1 (order T R)
            H2 (forall [X (set T)]
                   (exists [u T] (lub T R X u)))]
       (have a (antisymmetric T R) :by (p/%and-elim-right H1))
       (have b (forall [X (set T)]
                 (exists [l T] (glb T R X l)))
             :by ((all-lub-all-glb T R) a H2))
       (have c (complete-lattice T R) :by ((p/and-intro (order T R)
                                                        (forall [X (set T)]
                                                          (exists [l T] (glb T R X l)))) H1 b))
       (qed c)))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:qed</span>","value":":qed"},{"type":"html","content":"<span class='clj-symbol'>complete-lattice-from-lub</span>","value":"complete-lattice-from-lub"}],"value":"[:qed complete-lattice-from-lub]"}
;; <=

;; **
;;; This leads to an important dual property.
;; **

;; @@
(defthm inv-complete-lattice
  "The inverse of a complete lattice is a complete lattice."
  [[T :type] [R (rel T)]]
  (==> (complete-lattice T R)
       (complete-lattice T (inverse-rel T R))))
;; @@
;; =>
;;; {"type":"list-like","open":"<span class='clj-vector'>[</span>","close":"<span class='clj-vector'>]</span>","separator":" ","items":[{"type":"html","content":"<span class='clj-keyword'>:declared</span>","value":":declared"},{"type":"html","content":"<span class='clj-keyword'>:theorem</span>","value":":theorem"},{"type":"html","content":"<span class='clj-symbol'>inv-complete-lattice</span>","value":"inv-complete-lattice"}],"value":"[:declared :theorem inv-complete-lattice]"}
;; <=

;; @@
(proof inv-complete-lattice :script
    (assume [H (complete-lattice T R)]
       (have a (order T (inverse-rel T R)) :by ((inv-order T R) (p/%and-elim-left H)))
       (have b (forall [X (set T)]
                 (exists [l T] (glb T R X l))) :by (p/%and-elim-right H))
       (have c (antisymmetric T R) :by (p/%and-elim-right (p/%and-elim-left H)))
       (assume [X (set T)]
          (have d1 (exists [l T] (glb T R X l)) :by (b X))
          (have glbX-unique _ :by ((glb-unique T R X) c d1))
          (have glbX T :by (q/the T (lambda [l T] (glb T R X l)) glbX-unique))
          (have d2 (glb T R X glbX) :by (q/the-prop T (lambda [l T] (glb T R X l)) glbX-unique))
          (have d3 (lub T (inverse-rel T R) X glbX) :by ((inv-glb T R) X glbX d2))
          (have d4 (exists [u T] (lub T (inverse-rel T R) X u))
                :by ((q/ex-intro T (lambda [u T] (lub T (inverse-rel T R) X u)) glbX) d3))
          (have d (forall [X (set T)]
                    (exists [u T] (lub T (inverse-rel T R) X u))) :discharge [X d4]))
       (have e (complete-lattice T (inverse-rel T R))
             :by ((complete-lattice-from-lub T (inverse-rel T R))
                  a d))
       (qed e)))

;; @@

;; **
;;; TODO:
;;; 
;;;   
;;;   - show that a complete-lattice has a bottom (resp. a top)
;;;   
;; **

;; **
;;; ## Monotonous functions
;;; 
;;; TODO
;; **

;; **
;;; ## The fixed point theorem for monotonous functions on complete lattices
;;; 
;;; TODO
;; **

;; @@

;; @@
