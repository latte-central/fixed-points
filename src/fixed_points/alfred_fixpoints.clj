;; this is a working file for the nextjournal article

(ns fixed-points.alfred-fixpoints
  (:refer-clojure :exclude [and or not set =])
  (:require [clojure.repl :refer [source doc]]
            [latte.core
             :as latte
             :refer [defthm deflemma defimplicit definition example defaxiom
                     proof assume have pose qed
                     type-check? type-of forall]]
            [latte.utils :as u]
            [latte-prelude.fun :refer [injective surjective compose]]
            [latte-sets.core :refer [set elem set-equal emptyset forall-in] :as sets]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.prop :as p :refer [not and and* or absurd]]
            [latte-prelude.quant :refer [exists ex ex-elim] :as q]))


(definition reflexive
  [?T :type, R (rel T T)]
  (forall [x T] (R x x)))

(definition transitive
  [?T :type, R (rel T T)]
  (forall [x y z T]
    (==> (R x y)
         (R y z)
         (R x z))))

(definition antisymmetric
   [?T :type, R (rel T T)]
   (forall [x y T]
       (==> (R x y)
            (R y x)
            (equal x y))))

(definition order
  [?T :type, R (rel T T)]
  (and* (reflexive R)
        (transitive R)
        (antisymmetric R)))

(definition ridentity
   [T :type]
   (lambda [x T] (lambda [y T] (equal x y))))

(type-of [T :type]
   (ridentity T))
;; => (==> T T ✳)

(defthm rid-refl
  [T :type]
  (reflexive (ridentity T)))

(proof 'rid-refl
  "First, we take an arbitrary `x` o type `T`."
  (assume [x T]
    "A basic fact is that `x` is equal to itself."
    (have <a> (equal x x) :by (eq/eq-refl x))
    "Hence `x` is related to itself in the identity..."
    (have <b> ((ridentity T) x x) :by <a>))
  "After closing the assumption, we reach our goal 
since we took `x` arbitrarily."
  (qed <b>))

(defthm rid-trans
  [T :type]
  (transitive (ridentity T)))

(proof 'rid-trans
   (pose R := (ridentity T))
   (assume [x T y T z T
            Hxy (R x y)
            Hyz (R y z)]
     (have <a> (equal x y) :by Hxy)
     (have <b> (equal y z) :by Hyz)
     (have <c> (equal x z) :by (eq/eq-trans <a> <b>))
     (have <d> (R x z) :by <c>))
   (qed <d>))

(deflemma rid-antisym
   [T :type]
   (antisymmetric (ridentity T)))

(proof 'rid-antisym
  (pose R := (ridentity T))
  (assume [x T y T
           Hxy (R x y)
           Hyx (R y x)]
    (have <a> (equal x y) :by Hxy))
  (qed <a>))

(defthm rid-order 
  [T :type]
  (order (ridentity T)))

(proof 'rid-order
   (qed (p/and-intro* (rid-refl T) 
                      (rid-trans T)
                      (rid-antisym T))))

(definition rinverse
  [?T :type, R (rel T T)]
  (lambda [x T] (lambda [y T] (R y x))))


(defthm rinv-order 
  [?T :type, R (rel T T)]
  (==> (order R)
       (order (rinverse R))))

(proof 'rinv-order-thm
  (pose iR != (rinverse R))
  (assume [HR (order R)]

    "First part: reflexivity"

    (have <r> (reflexive R) :by (p/and-elim* 1 HR))
    "This is the same as the following."
    (have iR-refl (reflexive iR) :by <r>)

    "Second part: transitivity"

    (have R-trans (transitive R) :by (p/and-elim* 2 HR))
    "The assumptions for transitivity of `iR`."
    (assume [x T y T z T
             Hxy (iR x y)
             Hyz (iR y z)]
      "The two hypotheses can be rewritten in terms of `R`."
      (have <t1> (R y x) :by Hxy)
      (have <t2> (R z y) :by Hyz)
      "And we can exploit the fact that `R` is transitive."
      (have <t3> (R z x) :by (R-trans z y x <t2> <t1>))
      "Which is the same as the following:"
      (have <t> (iR x z) :by <t3>))
    (have iR-trans (transitive iR) :by <t>)

    "Third part: antisymmetry"
    
    (have R-anti (antisymmetric R) :by (p/and-elim* 3 HR))

    "Under the assumptions for antisymmetry of `iR`."
    (assume [x T y T
             Hxy (iR x y)
             Hyx (iR y x)]
      "We simply exploit the fact that e.g. `(iR x y)` is `(R y x)`."
      (have <s> (equal x y) :by (R-anti x y Hyx Hxy)))
    (have iR-anti (antisymmetric iR) :by <s>)

    "Thus the inverse is an ordering relation."
    (have iR-order (order iR) :by (p/and-intro* iR-refl iR-trans iR-anti)))

  (qed iR-order))


(definition lower-bound
   "`l` is a lower bound for `X` in the ordering relation `R`."
   [?T :type, R (rel T T), S (set T), l T]
   (forall-in [e S] (R l e)))

(definition upper-bound
"`u` is an upper bound for set `S` in the ordering relation `R`."
   [?T :type, R (rel T T), S (set T), u T]
   (forall-in [e S] (R e u)))

(defthm low-up-dual
   [?T :type, R (rel T T), S (set T), x T]
  (==> (lower-bound R S x)
       (upper-bound (rinverse R) S x)))

(proof 'low-up-dual-thm
  (pose iR := (rinverse R))
  "The hypothesis is that `x` is a lower bound."
  (assume [Hlow (lower-bound R S x)]
    "Now we take an arbitrary element `e` of the set `S`."
    (assume [e T
             He (elem e S)]
      "By hypothesis `x` is lower than `e` in `R`."
      (have <a> (R x e) :by (Hlow e He))
      "Hence it is greated in `iR`."
      (have <b> (iR e x) :by <a>))
    "And we're done."
    (have up (upper-bound iR S x) :by <b>))
  (qed up))

(definition least-element
   [?T :type, R (rel T T), S (set T), l T]
   (and (elem l S)
        (lower-bound R S l)))

(definition greatest-element
   [?T :type, R (rel T T), S (set T), u T]
   (and (elem u S)
        (upper-bound R S u)))

(definition glb
  "The greatest lower bound `l` of a subset `S` relation `R`."
   [?T :type, R (rel T T), S (set T), l T]
  (and (lower-bound R S l)
       (forall [x T]
          (==> (lower-bound R S x)
               (R x l)))))

(definition lub
  "The least upper bound `u` of a subset `S` in relation `R`."
  [?T :type, R (rel T T), S (set T), u T]  
  (and (upper-bound R S u)
       (forall [x T]
          (==> (upper-bound R S x)
               (R u x)))))

(defthm glb-lub-dual 
  [?T :type, R (rel T T)]
  (forall [S (set T)]
      (forall [l T]
         (==> (glb R S l)
              (lub (rinverse R) S l)))))

(proof 'glb-lub-dual-thm
   (pose iR := (rinverse R))
   "First let's state the main hypotheses."
   (assume [S (set T)
            l T
            Hl (glb R S l)]
      "From now on the inverse will be noted `R'`."
      "A `glb` is a lower bound..."
      (have <a1> (lower-bound R S l) :by (p/and-elim-left Hl))
      "... and thus is is an upper bound for the inverse,
which is the least part of the [[lub]] conjunction we need."
      (have <a> (upper-bound iR S l) :by ((low-up-dual R S l) <a1>))
      "Now let's assume we have `u` an upper bound in `R'`."
      (assume [u T
               Hu (upper-bound iR S u)]
        "We trivially have that `l` is lower than `u` in `iR'`
          (since it is greater in `R`)."
        (have <b> (iR l u) :by ((p/and-elim-right Hl) u Hu)))
   
      "Thus we have the right part of the [[lub]] conjunction." 
      (have <c> _ :by (p/and-intro <a> <b>)))
   
   "Hence we can conclude"
   (qed <c>))

(deflemma glb-single
  "Singleness of greateast lower bounds."
  [?T :type, R (rel T T), X (set T)]
  (==> (antisymmetric R)
       (q/single (lambda [l T] (glb R X l)))))

(proof 'glb-single-lemma
  (pose P := (lambda [l T] (glb R X l)))
  "These are all our assumptions:"
  (assume [Hanti (antisymmetric R) 
           l1 T, l2 T 
           H1 (P l1) H2 (P l2)]
    "We much show that l1 is equal to l2."
    "First, these are two lower bounds for `R`."
    (have <a> (lower-bound R X l1) :by (p/and-elim-left H1))
    (have <b> (lower-bound R X l2) :by (p/and-elim-left H2))
    "Now let's apply the *greatest* constraints."
    "First, `l1` is greater than `l2`."
    (have <c> (R l2 l1) :by ((p/and-elim-right H1) l2 <b>))
    "Second, `l2` is greater than `l1`."
    (have <d> (R l1 l2) :by ((p/and-elim-right H2) l1 <a>))
    "Thus, by antisymmetry (our hypothesis `H`) `l1` and `l2` must be equal."
    (have <e> (equal l1 l2) :by (Hanti l1 l2 <d> <c>)))
  "And this is enough to conclude"
  (qed <e>))


(defthm glb-unique
  "Unicity of greatest lower bounds."
  [?T :type, R (rel T T), X (set T)]
  (==> (antisymmetric R)
       (exists [l T] (glb R X l))
       (q/unique (lambda [l T] (glb R X l)))))

(proof 'glb-unique-thm
  (assume [Hanti _, Hex _]
    (have <a> _ :by (p/and-intro Hex ((glb-single R X) Hanti))))
  (qed <a>))


(defthm lub-unique-by-duality
  [?T :type, R (rel T T), X (set T)]
  (==> (antisymmetric R)
       (exists [l T] (glb R X l))
       (q/unique (lambda [l T] (lub R X l)))))

(proof 'lub-unique-by-duality-thm
  (assume [Hanti _, ]))
