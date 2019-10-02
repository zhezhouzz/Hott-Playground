From HoTT Require Export TypeTheory.

Definition inverseRefl (A: Type) (x y: A): (Identity A x y) -> (Identity A y x) :=
  indId A (fun x y _ => Identity A y x) (fun x => idRefl A x) x y.

Definition inverseReflSnd (A: Type) (x : A): (inverseRefl A x x (idRefl A x)) = idRefl A x := eq_refl.

(* refl_x o refl_x := refl_x *)
Definition compRefl (A: Type) (x y z: A): (Identity A x y) -> (Identity A y z) -> (Identity A x z) :=
  fun p =>
  indId A (fun x y _ => forall z, (Identity A y z) -> (Identity A x z))
        (indId A (fun x z _ => Identity A x z) (fun x => idRefl A x))
        x y p z.

(* refl_x o p := p *)
Definition compRefl' (A: Type) (x y z: A): (Identity A x y) -> (Identity A y z) -> (Identity A x z) :=
  indId A (fun x y _ => (Identity A y z) -> (Identity A x z))
        (fun _ => fun x => x) x y.

(* p o refl_x := p *)
Definition compRefl'' (A: Type) (x y z: A): (Identity A x y) -> (Identity A y z) -> (Identity A x z) :=
  fun p q =>
    indId A (fun y z _ => (Identity A x y) -> (Identity A x z)) (fun _ => fun x => x) y z q p.

Definition compReflSnd (A: Type) (x: A): compRefl A x x x (idRefl A x) (idRefl A x) = (idRefl A x) := eq_refl.

