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

(* Chapter 2.2 *)

Definition ap {A B: Type} {x y: A} (f: A -> B) (p: x =t y): (f x) =t (f y) :=
  Identity_rect _ (fun x y _ => (f x) =t (f y)) (fun x => =e (f x)) x y p.

Definition apSnd {A B: Type} {x: A} (f: A -> B): ap f (=e x) = =e (f x) := eq_refl.

Definition Lemma2_2_2_i {A B C: Type} {x y z: A} (f: A -> B) (g: B -> C) (p: x =t y) (q: y =t z): ap f (p =o= q) =t ((ap f p) =o= (ap f q)) :=
  Identity_rect
    _
    (fun x y p => forall (z: A) (q: y =t z), ap f (p =o= q) =t ((ap f p) =o= (ap f q)))
    (fun x z q =>
       Identity_rect
         _
         (fun x z q => ap f ((=e x) =o= q) =t ((ap f (=e x)) =o= (ap f q)))
         (fun x => =e =e (f x))
         x z q
    ) x y p z q.

Definition Lemma2_2_2_ii {A B: Type} {x y: A} (f: A -> B) (p: x =t y): ap f (=~ p) =t =~ (ap f p) :=
  Identity_rect
    _
    (fun x y p => ap f (=~ p) =t =~ (ap f p))
    (fun x => =e =e (f x))
    x y p.

Definition Lemma2_2_2_iii {A B C: Type} {x y: A} (f: A -> B) (g: B -> C) (p: x =t y): ap g (ap f p) =t (ap (fun x => g (f x)) p) :=
  Identity_rect
    _
    (fun x y p => ap g (ap f p) =t (ap (fun x => g (f x)) p))
    (fun x => =e =e (g (f x)))
    x y p.

Definition Lemma2_2_2_iv {A B: Type} {x y: A} (f: A -> B) (p: x =t y): ap (fun x => x) p =t p :=
  Identity_rect
    _
    (fun x y p => ap (fun x => x) p =t p)
    (fun x => =e =e x)
    x y p.

(* Chapter 2.3 *)

Definition Transport {A: Type} {P: A -> Type} {x y: A} (p: x =t y): P x -> P y :=
  Identity_rect
    _
    (fun x y p => P x -> P y)
    (fun _ k => k)
    x y p.

Definition TransportSnd {A: Type} {P: A -> Type} {x: A}: Transport (=e x) = (fun x: P x => x) := eq_refl.

Notation "=* p" := (Transport p) (at level 80, right associativity).

Notation "pr-1 p" := (sig1 _ _ p) (at level 80, right associativity).
Notation "pr-2 p" := (sig2 _ _ p) (at level 80, right associativity).
Notation "sig* x y" := (Sig _ _ x y) (at level 80, right associativity).

Definition lift {A: Type} {P: A -> Type} (e: Sigma A P) {y: A} (p: (pr-1 e) =t y): e =t Sig _ _ y ((=* p) (pr-2 e)) :=
  Sigma_rect
    _ _
    (fun e => forall (y: A) (p: (pr-1 e) =t y), e =t Sig _ _ y ((=* p) (pr-2 e)))
    (fun x u y p =>
       Identity_rect
         _
         (fun x y p => forall u, (Sig _ _ x u) =t Sig _ _ y ((=* p) u))
         (fun x u => =e (Sig _ _ x u))
         x y p u
    )
    e y p.

Definition path_lift {A: Type} {P: A -> Type} (e: Sigma A P) {y: A} (p: (pr-1 e) =t y): ap (fun x => sig1 _ _ x) (lift e p) =t p :=
  Sigma_rect
    _ _
    (fun e => forall (y: A) (p: (pr-1 e) =t y), ap (fun x => sig1 _ _ x) (lift e p) =t p)
    (fun x u y p =>
       Identity_rect
         _
         (fun x y p => forall u, ap (fun x => sig1 _ _ x) (lift (Sig _ _ x u) p) =t p)
         (fun x _ => =e =e x)
         x y p u
    )
    e y p.

Definition apd {A: Type} {P: A -> Type} {x y: A} (f: forall x: A, P x) (p: x =t y): (=* p) (f x) =t (f y) :=
  Identity_rect _ (fun x y p => (=* p) (f x) =t (f y)) (fun x => =e (f x)) x y p.

Definition apdSnd {A: Type} {P: A -> Type} {x: A} (f: forall x: A, P x) : apd f (=e x) = =e (f x) := eq_refl.

Definition Transportconst {A: Type} {B: Type} {x y: A} (p: x =t y) (b: B): Transport p b =t b :=
  Identity_rect _ (fun _ _ p => forall b: B, Transport p b =t b) (fun x b => =e b) x y p b.

Definition Lemma_2_3_8 {A B : Type} (f: A -> B) {x y: A} (p: x =t y): apd f p =t (Transportconst p (f x)) =o= (ap f p) :=
  Identity_rect
    _
    (fun x y p => apd f p =t (Transportconst p (f x)) =o= (ap f p))
    (fun x => =e =e (f x))
    x y p.

Definition Lemma_2_3_9 {A: Type} {P: A -> Type} {x y z: A} (p: x =t y) (q: y =t z) (u: P x): (=* q) ((=* p) u) =t (=* p =o= q) u :=
Identity_rect
  _
  (fun x y p => forall (z: A) (q: y =t z) (u: P x), (=* q) ((=* p) u) =t (=* p =o= q) u)
  (fun x z q u =>
     Identity_rect
       _
       (fun x z q => forall u: P x, (=* q) ((=* =e x) u) =t (=* (=e x) =o= q) u)
       (fun x u => =e u)
       x z q u
  )
  x y p z q u.

Definition Lemma_2_3_10 {A B: Type} (f: A -> B) (P: B -> Type) {x y: A} (p: x =t y) (u: P (f x)): (@Transport _ (fun x => P (f x)) _ _ p u) =t (=* (ap f p)) u:=
Identity_rect
  _
  (fun x y p => forall u: P (f x), (@Transport _ (fun x => P (f x)) _ _ p u) =t (=* (ap f p)) u)
  (fun x u => =e u)
  x y p u.

Definition Lemma_2_3_11 {A: Type} (P Q: A -> Type) (f: forall x: A, P x -> Q x) {x y: A} (p: x =t y) (u: P x): (=* p) (f x u) =t (f y ((=* p) u)) :=
Identity_rect
  _
  (fun x y p => forall u: P x, (=* p) (f x u) =t (f y ((=* p) u)))
  (fun x u => =e (f x u))
  x y p u.