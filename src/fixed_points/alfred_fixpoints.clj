;; this is a working file for the nextjournal article

(ns fixed-points.alfred-fixpoints
  (:refer-clojure :exclude [and or not set =])
  (:require [clojure.repl :refer [source doc]]
            [latte.core
             :as latte
             :refer [definition defthm deflemma
                     proof assume have pose qed
                     type-of forall]]
            [latte-sets.core :as sets :refer [set elem set-equal forall-in]]
            [latte-sets.rel :as rel :refer [rel]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.prop :as p :refer [not and and* or]]
            [latte-prelude.quant :as q :refer [exists]]))

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


(comment
(defthm lub-unique-by-duality
  [?T :type, R (rel T T), X (set T)]
  (==> (antisymmetric R)
       (exists [l T] (glb R X l))
       (q/unique (lambda [l T] (lub R X l)))))

(proof 'lub-unique-by-duality-thm
  (assume [Hanti _, ]))
)

(definition complete-lattice
  "The definition of a relation `R` on `T` being a complete lattice."
  [?T :type, R (rel T T)]
  (and (order R)
       (forall [X (set T)]
          (exists [l T] (glb R X l)))))

(defthm all-glb-all-lub
  [?T :type, R (rel T T)]
  (==> (antisymmetric R)
       (forall [X (set T)]
               (exists [l T] (glb R X l)))
       (forall [X (set T)]
               (exists [u T] (lub R X u)))))

(proof 'all-glb-all-lub-thm
  "First we introduce our two assumptions."
  (assume [H1 _ H2 _]
    "Now let's assume an arbitrary set `X`."
    (assume [X (set T)]
      "We define `Y` the set of upper bounds of `X`."
      (pose Y := (lambda [u T] (upper-bound R X u)))
      "By hypothesis there is a unique greatest lower bound for `Y`."
      (have <a> (exists [l T] (glb R Y l)) :by (H2 Y))
      (have glbY-unique _ :by ((glb-unique R Y) H1 <a>))
      "Let's call this `glbY`."
      (pose glbY := (q/the (lambda [l T] (glb R Y l)) glbY-unique))
      "And we keep the fact that it is indeed *the* greatest lower bound."
      (have <b> (glb R Y glbY) :by (q/the-prop (lambda [l T] (glb R Y l)) glbY-unique))

      "Our objective now is to show that `glbY` is *also* an upper bound for the set `X`."
      "For this we assume an arbitrary element `x` of the set `X`."
      (assume [x T
               Hx (elem x X)]
        
        "In the first step we'll show that `x` is a lower bound for `Y`."
        (assume [y T
                 Hy (elem y Y)]
          (have <c1> (upper-bound R X y) :by Hy)
          (have <c2> (R x y) :by (<c1> x Hx)))
        (have <c> (lower-bound R Y x) :by <c2>)

        "Hence since `glbY` is *greatest* we can show that `(R x glbY)`."
        (have <d1> (forall [z T]
                     (==> (lower-bound R Y z)
                          (R z glbY))) :by (p/and-elim-right <b>))
        
        (have <d2> (==> (lower-bound R Y x)
                        (R x glbY)) :by (<d1> x))
        
        (have <d3> (R x glbY) :by (<d2> <c>)))

      "Thus `glbY` is an upper bound for `X`."
      (have <d> (upper-bound R X glbY) :by <d3>)
      
      "The second step consists in showing that `glbY` is the *least* upper bound."
      (assume [x T
               Hx (upper-bound R X x)]

        "Taking an arbitrary upper bound `x`, we can show `(R glbY x)` since
as a `glbY` is a lower bound for `Y` and the assumed `x` is by hypothesis a member of `Y`. "
        
        (have <e1> (elem x Y) :by Hx)
        (have <e2> (lower-bound R Y glbY) :by (p/and-elim-left <b>))
        (have <e3> (R glbY x) :by (<e2> x <e1>)))
      
      (have <e> (forall [x T]
                  (==> (upper-bound R X x)
                       (R glbY x))) :by <e3>)
      
      "Hence we have our main result which is that `glbY` is a `lub` for `X`."
      (have <f> (lub R X glbY) :by (p/and-intro <d> <e>))

      "Hence we've just shown that there exists a lub for `X`, namely `glbY`."
      (have <g> (exists [l T] (lub R X l))
            :by ((q/ex-intro (lambda [l T] (lub R X l)) glbY) <f>))))

    (qed <g>))



(definition complete-lattice-alt
  [?T :type, R (rel T T)]
  (and (order R)
       (forall [X (set T)]
          (exists [l T] (lub R X l)))))

(defthm complete-lattice-glb-lub
  [?T :type, R (rel T T)]
  (==> (complete-lattice R)
       (complete-lattice-alt R)))


(proof 'complete-lattice-glb-lub-thm
  (assume [H _]
    "Let's dig out the antisymmetric property"
    (have <a> (antisymmetric R) 
          :by (p/and-elim* 3 (p/and-elim-left H)))
    "As well as the *all glb's* property"
    (pose glb-prop := (p/and-elim-right H))
    (have <b> (forall [X (set T)]
                (exists [l T] (lub R X l)))
          :by ((all-glb-all-lub R) <a> glb-prop))
    "and we're done"
    (have <c> (complete-lattice-alt R)
          :by (p/and-intro (p/and-elim-left H) <b>)))
  (qed <c>))


(definition monotonic
  "The endo function `f` on `T` is monotonic wrt. `R`."
  [?T :type, R (rel T T), f (==> T T)]
  (forall [x y T]
      (==> (R x y) (R (f x) (f y)))))


(defthm inv-monotonic
  [?T :type, R (rel T T), f (==> T T)]
  (==> (monotonic R f)
       (monotonic (rinverse R) f)))


(proof 'inv-monotonic-thm
  (pose R' := (rinverse R))
  (assume [H (monotonic R f)]
    (assume [x T
             y T
             H' (R' x y)]
      (have <a> (R y x) :by H')
      (have <b> (R (f y) (f x)) :by ((H y x) <a>))
      (have <c> (R' (f x) (f y)) :by <b>))
    (have <d> (monotonic R' f) :by <c>))
  (qed <d>))


(definition fixed-point
  "A fixed point `x` of an endo function `f` on `T`."
  [?T :type, f (==> T T), x T]
  (equal x (f x)))


(definition pre-fixed-point
  [?T :type, R (rel T T), f (==> T T), x T]
  (R x (f x)))

(definition post-fixed-point
  [?T :type, R (rel T T), f (==> T T), x T]
  (R (f x) x))


(defthm pre-post-fixed-point
  [?T :type, R (rel T T), f (==> T T), x T]
  (==> (antisymmetric R)
       (pre-fixed-point R f x)
       (post-fixed-point R f x)
       (fixed-point f x)))


(proof 'pre-post-fixed-point-thm
   (assume [H1 (antisymmetric R)
            H2 (pre-fixed-point R f x)
            H3 (post-fixed-point R f x)]
      (have <a> (fixed-point f x)
            :by (H1 x (f x) H2 H3)))
   (qed <a>))



(defthm fixed-point-post
  [?T :type, R (rel T T), f (==> T T), x T]
  (==> (reflexive R)
       (fixed-point f x)
       (post-fixed-point R f x)))

(proof 'fixed-point-post-thm
  (pose P := (lambda [y T] (R y x)))
  (assume [H1 (reflexive R) 
           H2 (fixed-point f x)]
    "Reflexivity means `(R x x)` hence `(P x)`."
    (have <a> (P x) :by (H1 x))
    "Since `(equal x (f x))` we can substitute in `(P x)` we just obtained."
    (have <b> (P (f x)) :by (eq/eq-subst P H2 <a>)))
  "And we're done"
  (qed <b>))


(definition lfp
  "The least fixed point of a function `f` wrt. a relation `R`."
  [?T :type, R (rel T T), f (==> T T), mu T]
  (and (fixed-point f mu)
       (forall [y T]
           (==> (fixed-point f y)
                (R mu y)))))

(defthm lfp-theorem
  "The least fixed-point theorem."
  [?T :type, R (rel T T), f (==> T T)]
  (==> (complete-lattice R)
       (monotonic R f)
       (q/unique (lambda [mu T] (lfp R f mu)))))

(deflemma lfp-ex
  "The least fixed-point theorem, existential part."
  [?T :type, R (rel T T), f (==> T T)]
  (==> (complete-lattice R)
       (monotonic R f)
       (exists [mu T] (lfp R f mu))))


(proof 'lfp-ex-lemma
  (assume [H1 _ H2 _]
    "We first define the set of post-fixed points of `F`."
    (pose Y := (lambda [y T] (post-fixed-point R f y)))
    "This set has a glb since `R` is a complete lattice."
    (have glbY-ex (exists [l T] (glb R Y l))
          :by ((p/and-elim-right H1) Y))
    (pose glbY-unique := ((glb-unique R Y)
                             (p/and-elim-right (p/and-elim-left H1))
                             glbY-ex))
    "We name it `glbY`."
    (pose glbY := (q/the (lambda [l T] (glb R Y l)) glbY-unique))
    "And we recall the main property."
    (have <a> (glb R Y glbY)
          :by (q/the-prop (lambda [l T] (glb R Y l)) glbY-unique))

    "In the first part we will show that `glbY` is a fixed point of `f`."
    
    "For this, we take an arbitrary elment `y` of `Y` 
(hence an arbitrary post-fixed point)."
    (assume [y T
             Hy (elem y Y)]
      "It is greater than a lower bound, e.g. `glbY`."
      (have <b1> (R glbY y) :by ((p/and-elim-left <a>) y Hy))
      "And thus by monotonicity:"
      (have <b2> (R (f glbY) (f y)) :by (H2 glbY y <b1>))
      "And it is also a post-fixed point, hence :"
      (have <b3> (R (f y) y) :by Hy)
      "Now, by transitivity:"
      (have <b4> (R (f glbY) y) :by
            ((p/and-elim-right (p/and-elim-left (p/and-elim-left H1)))
             (f glbY) (f y) y <b2> <b3>))
      "Thus `(f glbY)` is a lower bound of `Y`.")
    (have <b> (lower-bound R Y (f glbY)) :by <b4>)
    
    "Moreover, because `glbY` is a greatest lower bound."
    (have <c> (R (f glbY) glbY) :by ((p/and-elim-right <a>) (f glbY) <b>))
    "And since `f` is monotonous."
    (have <d1> (R (f (f glbY)) (f glbY)) :by (H2 (f glbY) glbY <c>))
    (have <d> (elem (f glbY) Y) :by <d1>)

    "Now `glbY` is still a lower bound, thus:"
    (have <e> (R glbY (f glbY)) :by ((p/and-elim-left <a>) (f glbY) <d>))
    "Thus `glbY` is a fixed point of `f`, since it is both a pre and a post-fixed point."
    (have <f> (fixed-point f glbY)
          :by ((pre-post-fixed-point R f glbY)
               (p/and-elim-right (p/and-elim-left H1))
               <e> <c>))

    "For the second part, we need to show that `glbY` is the *least* fixed point."

    (assume [z T
             Hz (fixed-point f z)]
            
        "A fixed point `z` is also a post-fixed point."
        (have <g1> (post-fixed-point R f z) 
              :by ((fixed-point-post R f z)
                   (p/and-elim* 1 (p/and-elim-left H1))
                   Hz))

        "Hence `z` is a member of the set `Y`..."
        (have <g2> (elem z Y) :by <g1>)
        "... which `glbY` (our fixed point) is a (greatest) lower bound, hence the following:"
        (have <g3> (R glbY z) :by ((p/and-elim-left <a>) z <g2>)))

    "hence we have the *least* property."
    (have <g> (forall [z T]
                (==> (fixed-point f z)
                     (R glbY z))) :by <g3>)

    "Now we obtained the `lfp` property for `glbY`."
    (have <h> (lfp R f glbY)
          :by (p/and-intro <f> <g>))

    "Which leads to the existential conclusion."
    (have <lfp> _ :by ((q/ex-intro (lambda [mu T] (lfp R f mu)) glbY) <h>)))

  (qed <lfp>))


(deflemma lfp-single
  [?T :type, R (rel T T), f (==> T T)]
  (==> (antisymmetric R)
       (q/single (lambda [mu T] (lfp R f mu)))))


(proof 'lfp-single-lemma
  (assume [H (antisymmetric R)]
    "We consider two least fixed point `mu1` and `mu2`."
    (assume [mu1 T
             mu2 T
             Hmu1 (lfp R f mu1)
             Hmu2 (lfp R f mu2)]
      "They are by definition of `lfp` interrelated in `R`."
      (have <a> (R mu1 mu2) :by ((p/and-elim-right Hmu1) mu2 (p/and-elim-left Hmu2)))
      (have <b> (R mu2 mu1) :by ((p/and-elim-right Hmu2) mu1 (p/and-elim-left Hmu1)))
      "Hence by antisymmetry they are equal."
      (have <c> (equal mu1 mu2) :by (H mu1 mu2 <a> <b>))))

  (qed <c>))

(proof 'lfp-theorem-thm
  (assume [H1 _ H2 _]
    (have <a> _ :by (p/and-intro 
                     ;; existence
                     ((lfp-ex R f) H1 H2)
                     ;; unicity
                     ((lfp-single R f) (p/and-elim* 3 (p/and-elim-left H1))))))
  (qed <a>))
                      

(definition gfp
  "The greatest fixed point of a function `f` wrt. a relation `R`."
  [?T :type, R (rel T T), f (==> T T), nu T]
  (and (fixed-point f nu)
       (forall [y T]
           (==> (fixed-point f y)
                (R y nu)))))

(defthm gfp-theorem
  "The greatest fixed-point theorem."
  [?T :type, R (rel T T), f (==> T T)]
  (==> (complete-lattice R)
       (monotonic R f)
       (q/unique (lambda [nu T] (gfp R f nu)))))


