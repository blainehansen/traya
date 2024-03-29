Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Cpdt.CpdtTactics.
Require Import PeanoNat Lt.
Require Import micromega.Lia.

Require Import core.utils.

(*Definition TotalAlignBool lt lu :=
	{TotalAlign lt lu} + {~(TotalAlign lt lu)}.
Obligation Tactic := crush.
Fixpoint lists_align
	(aligner: forall t u, {Align t u} + {~(Align t u)})
	lt lu
: TotalAlignBool lt lu :=
	match lt, lu with
	| [], [] => Yes
	| (t :: lt'), (u :: lu') => if aligner t u
		then Reduce (lists_align aligner lt' lu')
		else No
	| _, _ => No
	end.*)


(*
skipn_O: forall (l), skipn 0 l = l
skipn_all: forall (l), skipn (length l) l = []
skipn_nil: forall (n), skipn n ([]) = []
skipn_length: forall (n) (l), length (skipn n l) = length l - n
skipn_cons: forall (n) (a: A) (l), skipn (S n) (a :: l) = skipn n l
skipn_all2: forall [n] (l), length l <= n -> skipn n l = []
skipn_app: forall (n) (l1 l2), skipn n (l1 ++ l2) = skipn n l1 ++ skipn (n - length l1) l2

firstn_all: forall (l), firstn (length l) l = l
firstn_O: forall (l), firstn 0 l = []
firstn_le_length: forall (n) (l), length (firstn n l) <= n
firstn_nil: forall (n), firstn n [] = []
removelast_firstn_len: forall (l), removelast l = firstn (Init.Nat.pred (length l)) l
firstn_length: forall (n) (l), length (firstn n l) = Init.Nat.min n (length l)
firstn_all2: forall [n] (l), length l <= n -> firstn n l = l
firstn_skipn: forall (n) (l), firstn n l ++ skipn n l = l
firstn_length_le: forall (l) [n], n <= length l -> length (firstn n l) = n
firstn_cons: forall (n) (a: A) (l), firstn (S n) (a :: l) = a :: firstn n l
firstn_skipn_comm: forall (m n) (l), firstn m (skipn n l) = skipn n (firstn (n + m) l)
skipn_firstn_comm: forall (m n) (l), skipn m (firstn n l) = firstn (n - m) (skipn m l)
firstn_removelast: forall [n] (l), n < length l -> firstn n (removelast l) = firstn n l
firstn_app_2: forall (n) (l1 l2), firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2
firstn_app: forall (n) (l1 l2), firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2

*)


Section ListAlignment.
	Variable T U: Type.
	Variable Align: T -> U -> Prop.

	(* definition of Diverge *)
	Inductive Diverge: list T -> list U -> Prop :=
		| Diverge_nil: forall (t: T) lt, Diverge (t :: lt) (@nil U)
		| Diverge_cons: forall (t: T) (u: U) lt lu,
			~(Align t u) -> Diverge (t :: lt) (u :: lu)
	.

	(* properties of Diverge *)
	Theorem Diverge_divergent_not_empty lt lu: Diverge lt lu -> lt <> [].
	Proof.
		inversion 1; crush.
	Qed.

	Theorem Diverge_head_not_align lt lu:
		Diverge lt lu
			-> lu = []
				\/ exists (Hlt: 0 < length lt) (Hlu: 0 < length lu),
					~(Align (safe_nth lt Hlt) (safe_nth lu Hlu)).
	Proof.
		inversion 1 as [| ?? lt' lu'];
		unshelve eauto using Nat.lt_0_succ; crush.
	Qed.


	(* definition of TotalAlign *)
	Inductive TotalAlign: list T -> list U -> Prop :=
		| TotalAlign_nil: TotalAlign (@nil T) (@nil U)
		| TotalAlign_cons: forall (t: T) (u: U) lt lu,
			Align t u -> TotalAlign lt lu -> TotalAlign (t :: lt) (u :: lu)
	.
	Hint Constructors TotalAlign: core.

	(* properties of TotalAlign *)
	Theorem TotalAlign_contradicts_Diverge lt lu:
		TotalAlign lt lu -> ~(Diverge lt lu).
	Proof.
		inversion 1; inversion 1; crush.
	Qed.
	Theorem Diverge_contradicts_TotalAlign lt lu:
		Diverge lt lu -> ~(TotalAlign lt lu).
	Proof.
		intros ? HA;
		apply (contrapositive (TotalAlign_contradicts_Diverge HA)); crush.
	Qed.

	Theorem TotalAlign_same_length lt lu:
		TotalAlign lt lu -> length lt = length lu.
	Proof.
		induction 1; crush.
	Qed.

	Ltac remember_TotalAlign :=
		repeat match goal with
		| H: TotalAlign ?lt ?lu |- _ =>
			match goal with | _: lt = ?a, _: lu = ?b |- _ => fail 2 end
			|| remember lt; remember lu
		end.

	Ltac add_TotalAlign_same_length :=
		repeat match goal with
		| H: TotalAlign ?lt ?lu |- _ =>
			first [notHyp (length lt = length lu) | fail 2]
			|| specialize (TotalAlign_same_length H) as ?
		end.

	Theorem TotalAlign_append lt_one lu_one lt_two lu_two:
		TotalAlign lt_one lu_one
		-> TotalAlign lt_two lu_two
		-> TotalAlign (lt_one ++ lt_two) (lu_one ++ lu_two).
	Proof.
		Hint Rewrite -> app_nil_r.
		induction 1; induction 1; crush.
	Qed.

	Theorem TotalAlign_nth_C n lt lu:
		TotalAlign lt lu
		-> n < length lt \/ n < length lu
		-> exists (Hlt: n < length lt) (Hlu: n < length lu),
			Align (safe_nth lt Hlt) (safe_nth lu Hlu).
	Proof.
		intros HC [Hlt | Hlu];
		add_TotalAlign_same_length;
		match goal with
		| HC: TotalAlign ?lt ?lu, HL: length ?lt = length ?lu |- _ =>
			match goal with
			| _: ?n < length lt |- _ =>
				assert (Hlu: n < length lu) by solve [rewrite <- HL; assumption]
			| _: ?n < length lu |- _ =>
				assert (Hlt: n < length lt) by solve [rewrite -> HL; assumption]
			end
		end;
		exists Hlt; exists Hlu;
		induction n; destruct lt, lu; inversion HC; crush.
	Qed.

	Theorem TotalAlign_split_lengths lt_one lu_one lt_two lu_two:
		TotalAlign (lt_one ++ lt_two) (lu_one ++ lu_two)
		-> length lt_one = length lu_one <-> length lt_two = length lu_two.
	Proof.
		intros; remember_TotalAlign;
		add_TotalAlign_same_length; add_append_length; crush.
	Qed.

	Ltac trivial_TotalAlign :=
		add_length_cons_equal;
		try match goal with
			| _: context[?l ++ []] |- _ => do 2 rewrite -> app_nil_r in *
		end;
		match goal with
			| |- TotalAlign [] [] =>
				solve [apply TotalAlign_nil]
			|
				AlignTU: Align ?t ?u,
				HC: TotalAlign ?lt ?lu
				|- TotalAlign (?t :: ?lt) (?u :: ?lu)
			=>
				solve [apply (TotalAlign_cons AlignTU HC)]

			| HL: length (?t :: ?lt) = length [] |- _ =>
				solve [simpl in HL; discriminate HL]
			| HL: length [] = length (?u :: ?lu) |- _ =>
				solve [simpl in HL; discriminate HL]

			| H: TotalAlign [] (?u :: ?lu) |- _ => solve [inversion H]
			| H: TotalAlign (?t :: ?lt) [] |- _ => solve [inversion H]
		end.

	Theorem TotalAlign_firstn n lt lu:
		TotalAlign lt lu
		-> TotalAlign (firstn n lt) (firstn n lu).
	Proof.
		intros HA; generalize dependent n; induction HA; intros []; crush.
	Qed.
	Theorem TotalAlign_skipn n lt lu:
		TotalAlign lt lu
			-> TotalAlign (skipn n lt) (skipn n lu).
	Proof.
		intros HA; generalize dependent n; induction HA; intros []; crush.
	Qed.
	Theorem TotalAlign_split n lt lu:
		TotalAlign lt lu
			-> TotalAlign (firstn n lt) (firstn n lu)
				/\ TotalAlign (skipn n lt) (skipn n lu).
	Proof.
		eauto using TotalAlign_firstn, TotalAlign_skipn.
	Qed.

	Theorem TotalAlign_append_split lt_one lu_one lt_two lu_two:
		TotalAlign (lt_one ++ lt_two) (lu_one ++ lu_two)
		-> length lt_one = length lu_one \/ length lt_two = length lu_two
		-> TotalAlign lt_one lu_one /\ TotalAlign lt_two lu_two.
	Proof.
		intros HA [HL | HL]; split;
		specialize (TotalAlign_firstn (length lt_one) HA) as H1;
		specialize (TotalAlign_skipn (length lt_one) HA) as H2;
		try match goal with
		| HC: TotalAlign _ _, HL: length ?lt_two = length ?lu_two
		|- _ =>
			apply (TotalAlign_split_lengths lt_one lu_one lt_two lu_two HC) in HL
		end;
		rewrite -> (firstn_length_append lt_one lt_two) in H1;
		first [rewrite -> HL in H1 | rewrite <- HL in H1];
		rewrite -> (firstn_length_append lu_one lu_two) in H1;
		rewrite -> (skipn_length_append lt_one lt_two) in H2;
		first [rewrite -> HL in H2 | rewrite <- HL in H2];
		rewrite -> (skipn_length_append lu_one lu_two) in H2;
		assumption.
	Qed.

	Theorem TotalAlign_extension extending extended rest aligned:
		extending = extended ++ rest
		-> TotalAlign extending aligned
		-> TotalAlign extended (firstn (length extended) aligned).
	Proof.
		intros ? HC; subst;
		apply (TotalAlign_firstn (length extended)) in HC;
		rewrite -> firstn_length_append in HC; assumption.
	Qed.


	(* definition of FrontAlign *)
	Inductive FrontAlign: list T -> list U -> Prop :=
		| FrontAlign_nil: forall lu, FrontAlign (@nil T) lu
		| FrontAlign_cons: forall (t: T) (u: U) lt lu,
			Align t u -> FrontAlign lt lu -> FrontAlign (t :: lt) (u :: lu)
	.
	Hint Constructors FrontAlign: core.

	(* properties of FrontAlign *)
	Theorem FrontAlign_contradicts_Diverge:
		forall lt lu, FrontAlign lt lu -> ~(Diverge lt lu).
	Proof.
		intros ? ? HA HD; inversion HA; inversion HD; crush.
	Qed.
	Theorem Diverge_contradicts_FrontAlign:
		forall lt lu, Diverge lt lu -> ~(FrontAlign lt lu).
	Proof.
		intros ? ? ? HA;
		apply (contrapositive (FrontAlign_contradicts_Diverge HA)); crush.
	Qed.

	Theorem FrontAlign_le_length:
		forall lt lu, FrontAlign lt lu -> length lt <= length lu.
	Proof.
		intros ? ? H; induction H; crush.
	Qed.

	Theorem FrontAlign_firstn_front:
		forall n lt lu, FrontAlign lt lu -> FrontAlign (firstn n lt) lu.
	Proof.
		intros ? ? ? HA; generalize dependent n; induction HA; intros []; crush.
	Qed.
	Theorem FrontAlign_firstn:
		forall n lt lu, FrontAlign lt lu -> FrontAlign (firstn n lt) (firstn n lu).
	Proof.
		intros ? ? ? HA; generalize dependent n; induction HA; intros []; crush.
	Qed.
	Theorem FrontAlign_skipn:
		forall n lt lu, FrontAlign lt lu -> FrontAlign (skipn n lt) (skipn n lu).
	Proof.
		intros ? ? ? HA; generalize dependent n; induction HA; intros []; crush.
	Qed.

	Theorem FrontAlign_extension:
		forall extending extended rest aligned,
			extending = extended ++ rest
			-> FrontAlign extending aligned
			-> FrontAlign extended aligned.
	Proof.
		intros ? ? ? ? ? HM; subst; generalize dependent aligned;
		induction extended; intros; destruct aligned; inversion HM; crush.
	Qed.
	Theorem FrontAlign_extension_contrapositive:
		forall extending extended rest aligned,
			extending = extended ++ rest
			-> ~(FrontAlign extended aligned)
			-> ~(FrontAlign extending aligned).
	Proof.
		intros ? ? ? ? Hb ?;
		apply (contrapositive (@FrontAlign_extension extending extended _ _ Hb));
		assumption.
	Qed.


	(* relationships between TotalAlign and FrontAlign *)
	Theorem TotalAlign_FrontAlign:
		forall lt lu, TotalAlign lt lu -> FrontAlign lt lu.
	Proof.
		intros ? ? H; induction H; crush.
	Qed.
	Hint Resolve TotalAlign_FrontAlign: core.

	Theorem FrontAlign_same_length_TotalAlign:
		forall lt lu,
			FrontAlign lt lu
			-> length lt = length lu
			-> TotalAlign lt lu.
	Proof.
		intros ? ? H ?; induction H; destruct lu; crush.
	Qed.

	Theorem FrontAlign_lt_TotalAlign:
		forall lt lu, FrontAlign lt lu
			-> TotalAlign lt (firstn (length lt) lu).
	Proof.
		intros ? ? H; induction H; crush.
	Qed.
	Theorem FrontAlign_firstn_TotalAlign:
		forall n lt lu, FrontAlign lt lu
			-> n <= length lt
			-> TotalAlign (firstn n lt) (firstn n lu).
	Proof.
		intros ? ? ? HA Hlt; specialize (FrontAlign_le_length HA) as ?;
		apply (FrontAlign_firstn n) in HA; assert (Hlu: n <= length lu) by crush;
		specialize (firstn_length_le lt Hlt) as ?; specialize (firstn_length_le lu Hlu) as ?;
		assert (length (firstn n lt) = length (firstn n lu)) by crush;
		apply FrontAlign_same_length_TotalAlign; assumption.
	Qed.

	(* properties of prediction or lookahead *)
	Definition DivergesAt divergent against n :=
		TotalAlign (firstn n divergent) (firstn n against)
		/\ Diverge (skipn n divergent) (skipn n against).
	Hint Unfold DivergesAt: core.

	Hint Rewrite skipn_nil: core.
	Hint Rewrite firstn_nil: core.
	Hint Rewrite skipn_O: core.
	Hint Rewrite firstn_O: core.

	Theorem DivergesAt_divergent_longer:
		forall divergent against n,
			DivergesAt divergent against n -> n < length divergent.
	Proof.
		intros ?; induction divergent; intros ? ? [HA HD];
		destruct against; destruct n; inversion HD; inversion HA;
		try solve [apply lt_n_S; apply (IHdivergent against n); crush]; crush.
	Qed.
	Theorem DivergesAt_divergent_not_empty:
		forall divergent against n,
			DivergesAt divergent against n -> divergent <> [].
	Proof.
		intros ? ? ? [_ HD]; apply Diverge_divergent_not_empty in HD; crush.
	Qed.

	Theorem TotalAlign_contradicts_DivergesAt:
		forall divergent against n,
			TotalAlign divergent against -> ~(DivergesAt divergent against n).
	Proof.
		intros ? ? ? HA [_ HD];
		apply (TotalAlign_skipn n) in HA;
		apply (Diverge_contradicts_TotalAlign HD HA).
	Qed.
	Theorem DivergesAt_contradicts_TotalAlign:
		forall divergent against n,
			DivergesAt divergent against n -> ~(TotalAlign divergent against).
	Proof.
		intros ? ? ? ? HA;
		apply (contrapositive (@TotalAlign_contradicts_DivergesAt divergent against n HA)); crush.
	Qed.

	Theorem FrontAlign_contradicts_DivergesAt:
		forall divergent against n,
			FrontAlign divergent against -> ~(DivergesAt divergent against n).
	Proof.
		intros ? ? ? HA [_ HD];
		apply (FrontAlign_skipn n) in HA;
		apply (FrontAlign_contradicts_Diverge HA HD).
	Qed.
	Theorem DivergesAt_contradicts_FrontAlign:
		forall divergent against n,
			DivergesAt divergent against n -> ~(FrontAlign divergent against).
	Proof.
		intros ? ? ? ? HA;
		apply (contrapositive (@FrontAlign_contradicts_DivergesAt divergent against n HA)); crush.
	Qed.


	Definition Extends bigger smaller :=
		DivergesAt bigger smaller (length smaller).

	Theorem Extends_bigger_longer:
		forall bigger smaller,
			Extends bigger smaller -> length smaller < length bigger.
	Proof.
		intros ? ? HD; apply (DivergesAt_divergent_longer HD).
	Qed.
	(*
		when Align is equality, Extends implies
		smaller = (firstn (length smaller) bigger)
		/\ (skipn (length smaller) bigger) <> []
	*)

	Definition SomeAlignment divergent against n :=
		DivergesAt divergent against n /\ n <> 0.

	Theorem SomeAlignment_against_not_empty:
		forall divergent against n,
			SomeAlignment divergent against n -> against <> [].
	Proof.
		intros ? ? ? [[HA HD] ?];
		destruct divergent; destruct against; destruct n;
		inversion HD; inversion HA; crush.
	Qed.

	Definition NoAlignment divergent against :=
		DivergesAt divergent against 0.

	Theorem NoAlignment_equivalent_Diverge:
		forall divergent against,
			NoAlignment divergent against <-> Diverge divergent against.
	Proof.
		unfold NoAlignment; unfold DivergesAt; crush.
	Qed.

End ListAlignment.


Section ListEqualityAlignment.
	Variable T U: Type.
	Variable Align: T -> U -> Prop.

	Definition Equality (a b: T) := a = b.

End ListEqualityAlignment.


(*
Section FoldsAlignment.
	Variable T U: Type.
	Variable Align: T -> list U -> Prop.

	(* definition of FoldsAlign *)
	Inductive FoldsAlign: list T -> list U -> Prop :=
		| FoldsAlign_nil: FoldsAlign (@nil T) (@nil U)
		| FoldsAlign_cons: forall (t: T) (us: list U) lt lu,
			Align t us -> FoldsAlign lt lu -> FoldsAlign (t :: lt) (us ++ lu)
	.
	Hint Constructors FoldsAlign: core.


	(* definition of FoldsMatch *)
	Inductive FoldsMatch: list T -> list U -> Prop :=
		| FoldsMatch_nil: forall lu, FoldsMatch (@nil T) lu
		| FoldsMatch_cons: forall (t: T) (us: list U) lt lu,
			Align t us -> FoldsMatch lt lu -> FoldsMatch (t :: lt) (us ++ lu)
	.
	Hint Constructors FoldsMatch: core.

End FoldsAlignment.
*)
