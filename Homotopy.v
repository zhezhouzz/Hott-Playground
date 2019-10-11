From HoTT Require Export TypeTheory.

(* Chapter 2.1 *)

Notation "A =t B" := (Identity _ A B) (at level 80, right associativity).
Notation "=e x" := (idRefl _ x) (at level 80, right associativity).

Definition id_inv {A: Type} {x y: A}: (x =t y) -> (y =t x) :=
  indId A (fun x y _ => y =t x) (fun x => =e x) x y.

Notation "=~ x" := (id_inv x) (at level 80, right associativity).

Definition id_invSnd {A: Type} {x : A}: (=~ =e x) = =e x := eq_refl.

(* refl_x o refl_x := refl_x *)
Definition id_comp {A: Type} (x y z: A): (x =t y) -> (y =t z) -> (x =t z) :=
  fun p =>
    indId A (fun x y _ => forall z, (y =t z) -> (x =t z))
          (indId A (fun x z _ => x =t z) (fun x => =e x))
          x y p z.

Notation "p =o= q" := (id_comp _ _ _ p q) (at level 80, right associativity).

(* refl_x o p := p *)
Definition id_comp' (A: Type) (x y z: A): (x =t y) -> (y =t z) -> (x =t z) :=
  indId A (fun x y _ => (y =t z) -> (x =t z))
        (fun _ => fun x => x) x y.

(* p o refl_x := p *)
Definition id_comp'' (A: Type) (x y z: A): (x =t y) -> (y =t z) -> (x =t z) :=
  fun p q =>
    indId A (fun y z _ => (x =t y) -> (x =t z)) (fun _ => fun x => x) y z q p.

Definition id_compSnd (A: Type) (x: A): ((=e x) =o= =e x) = (=e x) := eq_refl.

(* Lemma 2.1.4 *)

Definition id_comp_1 (A: Type) (x y: A) (p: x =t y): p =t (p =o= =e y) :=
  Identity_rect A (fun x y p => p =t (p =o= =e y)) (fun x => =e =e x) x y p.

Definition id_comp_4  (A: Type) (x y z w: A) (p: x =t y) (q: y =t z) (r: z =t w): (p =o= (q =o= r)) =t (p =o= q) =o= r :=
  Identity_rect _
                (fun x y p => forall (z w: A) (q: y =t z) (r: z =t w), (p =o= (q =o= r)) =t (p =o= q) =o= r)
                (fun x z w q r =>
                   Identity_rect _
                                 (fun x z q => forall (w: A) (r: z =t w), ((=e x) =o= q =o= r) =t ((=e x) =o= q) =o= r)
                                 (fun x w r =>
                                    Identity_rect _
                                                  (fun x w r => ((=e x) =o= ((=e x) =o= r)) =t (((=e x) =o= =e x) =o= r))
                                                  (fun x => (=e =e x)
                                                  )
                                                  x w r

                                 )
                                 x z q w r
                )
                x y p z w q r.

Definition Omega {A: Type} (a: A) := a =t a.
Definition Omega2 {A: Type} (a: A) := (=e a) =t (=e a).
Definition compOmega1{A: Type} (a: A): Omega a -> Omega a -> Omega a := fun o1 o2 => o1 =o= o2.
Definition compOmega2{A: Type} (a: A): Omega2 a -> Omega2 a -> Omega2 a := fun o1 o2 => o1 =o= o2.

Definition ru {A: Type} {a b: A} (p: a =t b): p =t (p =o= =e b) :=
  Identity_rect _ (fun a b p => p =t (p =o= (=e b))) (fun a => (=e =e a)) a b p.
Definition ruSnd {A: Type} {a: A}: ru (=e a) = (=e =e a) := eq_refl.
Definition lu {A: Type} {a b: A} (p: a =t b): p =t ((=e a) =o= p) :=
  Identity_rect _ (fun a b p => p =t ((=e a) =o= p)) (fun a => (=e =e a)) a b p.
Definition luSnd {A: Type} {a: A}: lu (=e a) = (=e =e a) := eq_refl.
Definition comp_r {A: Type} {a b c: A} {p q: a =t b} (alpha: p =t q) (r: b =t c): (p =o= r) =t (q =o= r) :=
  Identity_rect _
                (fun b c r => forall (a: A) (p q: a =t b) (alpha: p =t q), (p =o= r) =t (q =o= r))
                (fun b a p q alpha => (=~ (ru p)) =o= alpha =o= (ru q))
                b c r a p q alpha.

Definition comp_rSnd {A: Type} {a b: A} {p q: a =t b} (alpha: p =t q): comp_r alpha (=e b) = ((=~ (ru p)) =o= alpha =o= (ru q)) := eq_refl.

Definition comp_l {A: Type} {a b c: A} {p q: b =t c} (r: a =t b) (beta: p =t q): (r =o= p) =t (r =o= q) :=
  Identity_rect _
                (fun a b r => forall (c: A) (p q: b =t c) (beta: p =t q), (r =o= p) =t (r =o= q))
                (fun b c p q beta => (=~ (lu p)) =o= beta =o= (lu q))
                a b r c p q beta.

Definition comp_lSnd {A: Type} {b c: A} {p q: b =t c} (beta: p =t q): comp_l (=e b) beta = ((=~ (lu p)) =o= beta =o= (lu q)) := eq_refl.

Definition compOmega2Snd {A: Type} (a: A) (alpha beta: Omega2 a): ((comp_r alpha (=e a)) =o= (comp_l (=e a) beta)) =t compOmega2 a alpha beta.
Proof.
  unfold compOmega2.
  assert ( (comp_r alpha (=e a) =o= comp_l (=e a) beta) = (((=~ (ru (=e a))) =o= alpha =o= (ru (=e a))) =o= ((=~ (lu (=e a))) =o= beta =o= (lu (=e a))))).
  rewrite <- comp_rSnd.
  rewrite <- comp_lSnd.
  reflexivity.
  rewrite luSnd in H.
  rewrite ruSnd in H.
  assert ((((=~ =e =e a) =o= alpha =o= =e =e a) =o= (=~ =e =e a) =o= beta =o= =e =e a)
          =t
             (((=~ =e =e a) =o= alpha) =o= ((=e =e a) =o= (=~ =e =e a)) =o= (beta =o= =e =e a))).
  admit. (* Lemma_2_1_4_iv *)
  assert (((=e =e a) =o= (=~ =e =e a)) = (=e =e a)). reflexivity.
  rewrite H0 in X. clear H0.
  assert ((=~ =e =e a) = =e =e a). reflexivity.
  rewrite H0 in X.
  assert ((((=e =e a) =o= alpha) =o= (=e =e a) =o= beta =o= =e =e a) =t (((=e =e a) =o= alpha) =o= beta =o= =e =e a)).
  admit. (* Lemma_2_1_4_i *)
  assert ((((=e =e a) =o= alpha) =o= beta =o= =e =e a) =t (((=e =e a) =o= alpha) =o= beta)).
  admit. (* Lemma_2_1_4_i *)
  assert ((((=e =e a) =o= alpha) =o= beta) =t (alpha =o= beta)).
  admit. (* Lemma_2_1_4_i *)
  rewrite H. clear H.
  apply id_comp with (((=e =e a) =o= alpha) =o= beta =o= =e =e a).
  apply (@eq_rect _ (=e =e a) (fun x => ((x =o= alpha =o= =e =e a) =o= x =o= beta =o= =e =e a) =t ((=e =e a) =o= alpha) =o= beta =o= =e =e a)); auto.
  apply id_comp with (((=e =e a) =o= alpha) =o= (=e =e a) =o= beta =o= =e =e a); auto.
  apply id_comp with (((=e =e a) =o= alpha) =o= beta); auto.
Admitted.

Definition compOmega2Trd {A: Type} (a: A) (alpha beta: Omega2 a): ((comp_l (=e a) beta) =o= (comp_r alpha (=e a))) =t compOmega2 a beta alpha.
Admitted.

Definition Eckmann_Hilton_Lemma {A: Type} (a: A) (alpha beta: Omega2 a):  (comp_r alpha (=e a) =o= comp_l (=e a) beta) =t comp_l (=e a) beta =o= comp_r alpha (=e a) :=
  Identity_rect
    _
    (fun p1 p2 alpha => forall beta: Omega2 a,  (comp_r alpha (=e a) =o= comp_l p2 beta) =t comp_l p1 beta =o= comp_r alpha (=e a))
    (fun p beta =>
       Identity_rect
         _
         (fun q1 q2 beta => (comp_r (=e p) q1 =o= comp_l p beta) =t comp_l p beta =o= comp_r (=e p) q2)
         (fun q =>
            Identity_rect
              _
              (fun _ _ p => forall q, (comp_r (=e p) q =o= comp_l p (=e q)) =t comp_l p (=e q) =o= comp_r (=e p) q)
              (fun a q =>
                 Identity_rect
                   _
                   (fun a _ q => (comp_r (=e =e a) q =o= comp_l (=e a) (=e q)) =t comp_l (=e a) (=e q) =o= comp_r (=e =e a) q)
                   (fun a => (=e (=e (=e a))))
                   a a q
              )
              a a p q
         )
         (=e a) (=e a) beta
    ) (=e a) (=e a) alpha beta.

Definition Eckmann_Hilton {A: Type} (a: A) (alpha beta: Omega2 a): compOmega2 a alpha beta =t compOmega2 a beta alpha.
Proof.
  apply id_comp with ((comp_r alpha (=e a)) =o= (comp_l (=e a) beta)).
  apply id_inv. apply compOmega2Snd.
  apply id_comp with ((comp_l (=e a) beta) =o= (comp_r alpha (=e a))).
  apply Eckmann_Hilton_Lemma.
  apply compOmega2Trd.
Qed.

