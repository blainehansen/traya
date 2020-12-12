```coq
Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extraction eq_nat_dec.

Recursive Extraction eq_nat_dec.



Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong: forall n: nat, n > 0 -> {m: nat | n = S m}. refine (
  fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end
  ); abstract crush.
Defined.


Obligation Tactic := crush.
Program Definition pred_strong' (n: nat) (_: n > 0): {m: nat | n = S m} :=
  match n with
    | O => _
    | S n' => n'
  end.


Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x || y" := (if x then Yes else Reduce y).

Section In_dec.
  Variable A: Set.
  Variable A_eq_dec: forall x y: A, {x = y} + {x <> y}.

  Definition In_dec: forall (x: A) (ls: list A), {In x ls} + {~ In x ls}.
    refine (fix f (x: A) (ls: list A): {In x ls} + {~ In x ls} :=
      match ls with
        | nil => No
        | x' :: ls' => A_eq_dec x x' || f x ls'
      end); crush.
  Defined.
End In_dec.


Inductive maybe (A: Set) (P: A -> Prop): Set :=
| Unknown: maybe P
| Found: forall x: A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).


Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Definition pred_strong8: forall n: nat, {m: nat | n = S m} + {n = 0}.
  refine (fun n =>
    match n with
      | O => !!
      | S n' => [||n'||]
    end); trivial.
Defined.


Inductive exp: Set :=
| Nat: nat -> exp
| Plus: exp -> exp -> exp
| Bool: bool -> exp
| And: exp -> exp -> exp.

Inductive type: Set := TNat | TBool.

Inductive hasType: exp -> type -> Prop :=
| HtNat: forall n,
  hasType (Nat n) TNat
| HtPlus: forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool: forall b,
  hasType (Bool b) TBool
| HtAnd: forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

Definition eq_type_dec: forall t1 t2: type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

Notation "x <- e1 ; e2" := (
  match e1 with
  | Unknown => ??
  | Found x _ => e2
  end
)
  (right associativity, at level 60).

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

Notation "x <-- e1 ; e2" := (
  match e1 with
    | inright _ => !!
    | inleft (exist x _) => e2
  end
)
  (right associativity, at level 60).

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).


Definition typeCheck: forall e: exp, {{t | hasType e t}}.
  Hint Constructors hasType: core.

  refine (fix F (e: exp): {{t | hasType e t}} :=
    match e return {{t | hasType e t}} with
      | Nat _ => [|TNat|]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;;
        eq_type_dec t2 TNat;;
        [|TNat|]
      | Bool _ => [|TBool|]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [|TBool|]
    end); crush.
Defined.


Lemma hasType_det: forall e t1,
  hasType e t1
  -> forall t2, hasType e t2
    -> t1 = t2.
  induction 1; inversion 1; crush.
Qed.


Definition typeCheck': forall e: exp,
  {t: type | hasType e t} + {forall t, ~ hasType e t}
.
  Hint Constructors hasType: core.
  Hint Resolve hasType_det: core.

  refine (
  fix F (e: exp): {t: type | hasType e t} + {forall t, ~ hasType e t} :=
    match e return {t: type | hasType e t} + {forall t, ~ hasType e t} with
      | Nat _ => [||TNat||]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [||TNat||]
      | Bool _ => [||TBool||]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [||TBool||]
    end
  ); clear F; crush' tt hasType; eauto.
Defined.
```
