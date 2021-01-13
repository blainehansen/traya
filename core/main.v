Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require String.
Require Import Cpdt.CpdtTactics.
Require Import PeanoNat Lt.

Require Import core.utils.

Ltac notHyp P :=
	match goal with
	| [ _ : P |- _ ] => fail 1
	| _ =>
		match P with
		| ?P1 /\ ?P2 => first [notHyp P1 | notHyp P2 | fail 2]
		| _ => idtac
		end
	end.

Ltac solve_assumption := try solve [assumption].

Theorem contrapositive: forall P Q: Prop,
	(P -> Q) -> (~Q -> ~P).
Proof. crush. Qed.

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
combine_firstn_r: forall [A B: Type] (l) (l': list B), combine l l' = combine (firstn (length l') l) l'
combine_firstn_l: forall [A B: Type] (l) (l': list B), combine l l' = combine l (firstn (length l) l')
removelast_firstn: forall [n] (l), n < length l -> removelast (firstn (S n) l) = firstn n l
firstn_app_2: forall (n) (l1 l2), firstn (length l1 + n) (l1 ++ l2) = l1 ++ firstn n l2
firstn_app: forall (n) (l1 l2), firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2

*)

Ltac rewrite_trivial_firstn_skipn :=
	try rewrite -> skipn_nil in *;
	try rewrite -> firstn_nil in *;
	try rewrite -> skipn_O in *;
	try rewrite -> firstn_O in *.

Theorem skipn_n_smaller_not_nil:
	forall T n (l: list T), n < length l -> skipn n l <> [].
Proof.
	intros ? n; induction n; intros l; induction l; intros; solve_crush;
	solve [simpl in *; apply IHn; crush].
Qed.

Theorem skipn_length_smaller_not_nil:
	forall T (bigger smaller: list T),
		length smaller < length bigger
		-> skipn (length smaller) bigger <> [].
Proof.
	intros; apply skipn_n_smaller_not_nil; crush.
Qed.

Theorem length_cons_equal:
	forall A B a (la: list A) b (lb: list B),
		length (a :: la) = length (b :: lb) -> length la = length lb.
Proof.
	intros; induction la; crush.
Qed.


Theorem firstn_length_append:
	forall T (l1 l2: list T), firstn (length l1) (l1 ++ l2) = l1.
Proof.
	intros; induction l1; crush.
Qed.
Theorem skipn_length_append:
	forall T (l1 l2: list T), skipn (length l1) (l1 ++ l2) = l2.
Proof.
	intros; induction l1; crush.
Qed.

Ltac add_append_length :=
	repeat match goal with
	| H: ?l = ?a ++ ?b |- _ =>
		first [notHyp (length (a ++ b) = length a + length b) | fail 2]
		|| specialize (app_length a b) as ?
	end.

Ltac add_length_cons_equal :=
	repeat match goal with
		| [ H: length (?t :: ?lt) = length (?u :: ?lu) |- _ ] =>
			first [notHyp (length lt = length lu) | fail 2]
			|| specialize (length_cons_equal H) as ?
	end.


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
	Theorem Diverge_main_not_empty:
		forall lt lu, Diverge lt lu -> lt <> [].
	Proof.
		intros ? ? HD; inversion HD; crush.
	Qed.

	Theorem Diverge_head_not_align:
		forall lt lu, Diverge lt lu
			-> lu = []
				\/ exists (Hlt: 0 < length lt) (Hlu: 0 < length lu),
					~(Align (safe_nth lt Hlt) (safe_nth lu Hlu)).
	Proof.
		intros ? ? HD; inversion HD as [| ? ? lt' lu'];
		try solve [left; reflexivity]; right;
		exists (Nat.lt_0_succ (length lt')); exists (Nat.lt_0_succ (length lu'));
		assumption.
	Qed.


	(* definition of TotalAlign *)
	Inductive TotalAlign: list T -> list U -> Prop :=
		| TotalAlign_nil: TotalAlign (@nil T) (@nil U)
		| TotalAlign_cons: forall (t: T) (u: U) lt lu,
			Align t u -> TotalAlign lt lu -> TotalAlign (t :: lt) (u :: lu)
	.
	Hint Constructors TotalAlign: core.

	(* properties of TotalAlign *)
	Theorem TotalAlign_contradicts_Diverge:
		forall lt lu, TotalAlign lt lu -> ~(Diverge lt lu).
	Proof.
		intros ? ? HA HD; inversion HA; inversion HD; crush.
	Qed.
	Theorem Diverge_contradicts_TotalAlign:
		forall lt lu, Diverge lt lu -> ~(TotalAlign lt lu).
	Proof.
		intros ? ? ? HA;
		apply (contrapositive (TotalAlign_contradicts_Diverge HA)); crush.
	Qed.

	Theorem TotalAlign_same_length:
		forall lt lu, TotalAlign lt lu -> length lt = length lu.
	Proof.
		intros ? ? H; induction H; crush.
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

	Theorem TotalAlign_append:
		forall lt_one lu_one lt_two lu_two,
			TotalAlign lt_one lu_one
			-> TotalAlign lt_two lu_two
			-> TotalAlign (lt_one ++ lt_two) (lu_one ++ lu_two).
	Proof.
		Hint Rewrite -> app_nil_r.
		intros ? ? ? ? H_one H_two; induction H_one; induction H_two; crush.
	Qed.

	Theorem TotalAlign_nth_C:
		forall n lt lu,
			TotalAlign lt lu
			-> n < length lt \/ n < length lu
			-> exists (Hlt: n < length lt) (Hlu: n < length lu),
				Align (safe_nth lt Hlt) (safe_nth lu Hlu).
	Proof.
		intros ? ? ? HC [Hlt | Hlu];
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
		generalize dependent lu; generalize dependent lt;
		induction n; intros; destruct lt; destruct lu; inversion HC; crush.
	Qed.

	Theorem TotalAlign_split_lengths:
		forall lt_one lu_one lt_two lu_two,
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

	Theorem TotalAlign_firstn:
		forall n lt lu, TotalAlign lt lu
			-> TotalAlign (firstn n lt) (firstn n lu).
	Proof.
		intros ? ? ? HA; generalize dependent n; induction HA; intros []; crush.
	Qed.
	Theorem TotalAlign_skipn:
		forall n lt lu, TotalAlign lt lu
			-> TotalAlign (skipn n lt) (skipn n lu).
	Proof.
		intros ? ? ? HA; generalize dependent n; induction HA; intros []; crush.
	Qed.
	Theorem TotalAlign_split:
		forall n lt lu, TotalAlign lt lu
			-> TotalAlign (firstn n lt) (firstn n lu)
				/\ TotalAlign (skipn n lt) (skipn n lu).
	Proof.
		intros ? ? ? H; split;
		try apply (TotalAlign_firstn n H);
		try apply (TotalAlign_skipn n H).
	Qed.

	Theorem TotalAlign_append_split:
		forall lt_one lu_one lt_two lu_two,
			TotalAlign (lt_one ++ lt_two) (lu_one ++ lu_two)
			-> length lt_one = length lu_one \/ length lt_two = length lu_two
			-> TotalAlign lt_one lu_one /\ TotalAlign lt_two lu_two.
	Proof.
		intros ? ? ? ? HA [HL | HL]; split;
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

	Theorem TotalAlign_shorter:
		forall bigger smaller extension align,
			bigger = smaller ++ extension
			-> TotalAlign bigger align
			-> TotalAlign smaller (firstn (length smaller) align).
	Proof.
		intros ? ? ? ? ? HC; subst;
		apply (TotalAlign_firstn (length smaller)) in HC;
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

	Theorem FrontAlign_shorter:
		forall bigger smaller extension aligned,
			bigger = smaller ++ extension
			-> FrontAlign bigger aligned
			-> FrontAlign smaller aligned.
	Proof.
		intros ? ? ? ? ? HM; subst; generalize dependent aligned;
		induction smaller; intros; destruct aligned; inversion HM; crush.
	Qed.
	Theorem FrontAlign_shorter_contrapositive:
		forall bigger smaller extension aligned,
			bigger = smaller ++ extension
			-> ~(FrontAlign smaller aligned)
			-> ~(FrontAlign bigger aligned).
	Proof.
		intros ? ? ? ? Hb ?;
		apply (contrapositive (@FrontAlign_shorter bigger smaller _ _ Hb));
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
	Definition DivergesAt main against n :=
		TotalAlign (firstn n main) (firstn n against)
		/\ Diverge (skipn n main) (skipn n against).
	Hint Unfold DivergesAt: core.

	Hint Rewrite skipn_nil: core.
	Hint Rewrite firstn_nil: core.
	Hint Rewrite skipn_O: core.
	Hint Rewrite firstn_O: core.

	Theorem DivergesAt_main_longer:
		forall main against n,
			DivergesAt main against n -> n < length main.
	Proof.
		intros ?; induction main; intros ? ? [HA HD];
		destruct against; destruct n; inversion HD; inversion HA;
		try solve [apply lt_n_S; apply (IHmain against n); crush]; crush.
	Qed.
	Theorem DivergesAt_main_not_empty:
		forall main against n,
			DivergesAt main against n -> main <> [].
	Proof.
		intros ? ? ? [_ HD]; apply Diverge_main_not_empty in HD; crush.
	Qed.

	Theorem TotalAlign_contradicts_DivergesAt:
		forall main against n,
			TotalAlign main against -> ~(DivergesAt main against n).
	Proof.
		intros ? ? ? HA [_ HD];
		apply (TotalAlign_skipn n) in HA;
		apply (Diverge_contradicts_TotalAlign HD HA).
	Qed.
	Theorem DivergesAt_contradicts_TotalAlign:
		forall main against n,
			DivergesAt main against n -> ~(TotalAlign main against).
	Proof.
		intros ? ? ? ? HA;
		apply (contrapositive (@TotalAlign_contradicts_DivergesAt main against n HA)); crush.
	Qed.

	Theorem FrontAlign_contradicts_DivergesAt:
		forall main against n,
			FrontAlign main against -> ~(DivergesAt main against n).
	Proof.
		intros ? ? ? HA [_ HD];
		apply (FrontAlign_skipn n) in HA;
		apply (FrontAlign_contradicts_Diverge HA HD).
	Qed.
	Theorem DivergesAt_contradicts_FrontAlign:
		forall main against n,
			DivergesAt main against n -> ~(FrontAlign main against).
	Proof.
		intros ? ? ? ? HA;
		apply (contrapositive (@FrontAlign_contradicts_DivergesAt main against n HA)); crush.
	Qed.


	Definition Extends bigger smaller :=
		DivergesAt bigger smaller (length smaller).

	Theorem Extends_bigger_longer:
		forall bigger smaller,
			Extends bigger smaller -> length smaller < length bigger.
	Proof.
		intros ? ? HD; apply (DivergesAt_main_longer HD).
	Qed.
	(*
		when Align is equality, Extends implies
		smaller = (firstn (length smaller) bigger)
		/\ (skipn (length smaller) bigger) <> []
	*)

	Definition SomeAlignment main against n :=
		DivergesAt main against n /\ n <> 0.

	Theorem SomeAlignment_against_not_empty:
		forall main against n,
			SomeAlignment main against n -> against <> [].
	Proof.
		intros ? ? ? [[HA HD] ?];
		destruct main; destruct against; destruct n;
		inversion HD; inversion HA; crush.
	Qed.

	Definition NoAlignment main against :=
		DivergesAt main against 0.

	Theorem NoAlignment_equivalent_Diverge:
		forall main against,
			NoAlignment main against <-> Diverge main against.
	Proof.
		unfold NoAlignment; unfold DivergesAt; crush.
	Qed.

End ListAlignment.

Section Lookahead.
	Variable T U: Type.
	Variable Equivalent: T -> T -> Prop.
	Variable compute_equivalent:
		forall t1 t2, {Equivalent t1 t2} + {~(Equivalent t1 t2)}.
	Variable Match: T -> U -> Prop.
	Variable compute_match:
		forall t u, {Match t u} + {~(Match t u)}.
	Variable equivalence_implies_match:
		forall t1 t2, Equivalent t1 t2 <-> (forall u, Match t1 u <-> Match t2 u).

	Definition EqDiverge := (Diverge Equivalent).
	Definition EqDivergesAt := (DivergesAt Equivalent).
	Definition EqExtends := (Extends Equivalent).
	Definition EqSomeAlignment := (SomeAlignment Equivalent).
	Definition EqTotalAlign := (TotalAlign Equivalent).
	Definition EqFrontAlign := (FrontAlign Equivalent).

	Definition MatchDiverge := (Diverge Match).
	Definition MatchDivergesAt := (DivergesAt Match).
	Definition MatchExtends := (Extends Match).
	Definition MatchSomeAlignment := (SomeAlignment Match).
	Definition MatchTotalAlign := (TotalAlign Match).
	Definition MatchFrontAlign := (FrontAlign Match).

	(*Theorem Equivalent_TotalAlign:
		forall lt1 lt2 lu,
			EqTotalAlign lt1 lt2
			<-> (MatchTotalAlign lt1 lu <-> MatchTotalAlign lt2 lu).
	Proof.
intros.
split; intros.
-
generalize dependent lu.
induction H; intros; destruct lu; solve_crush.
+
destruct lt; solve_crush; split; intros.
inversion H1.
subst.
apply TotalAlign_cons; try solve [assumption].
rename u into t2; rename t into t1; rename u0 into u.
apply (equivalence_implies_match t1 t2); assumption.

inversion H1.
subst.
apply TotalAlign_cons; try solve [assumption].
rename u into t2; rename t into t1; rename u0 into u.
apply (equivalence_implies_match t1 t2); assumption.

inversion H0.
inversion H0.

+
split; intros.

inversion H1.
subst.
apply TotalAlign_cons; try solve [assumption].
rename u into t2; rename t into t1; rename u0 into u.
apply (equivalence_implies_match t1 t2); assumption.

destruct (IHTotalAlign lu1) as [M _].
apply M.
assumption.

destruct (IHTotalAlign lu0) as [M _].

	Qed.*)

	(*Definition EqualityDiverge (T: Type) := (@Diverge T T (fun a b => a = b)).*)
	(*Definition DivergesAt main against n :=
		TotalAlign (firstn n main) (firstn n against)
		/\ Diverge (skipn n main) (skipn n against).*)
	Definition PredictsAgainst lookahead main against :=
		let n := (length lookahead) in
		lookahead = (firstn n main)
		/\ (
			EqDivergesAt against lookahead (n - 1)
			\/ EqExtends against main
			\/ EqTotalAlign against main
		).

	Theorem PredictsAgainst_correct_EqTotalAlign:
		forall lookahead main against matched n,
			(*let n := (length lookahead) in*)
			-> EqTotalAlign against main
			-> (MatchFrontAlign main matched -> MatchFrontAlign (firstn n main) matched)
				/\ (MatchFrontAlign against matched -> MatchFrontAlign main matched).
	Proof.

	Qed.

	Theorem PredictsAgainst_correct:
		forall lookahead main against matched,
			PredictsAgainst lookahead main against
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (
					(MatchFrontAlign lookahead matched -> ~(MatchFrontAlign against matched))
					\/ (MatchFrontAlign against matched -> MatchFrontAlign main matched)
				).
	Proof.
intros ? ? ? ? [HL [[HA HD] | [[HA HD] | HA]]]; split; try intros HM.

-
destruct main;
destruct against;
destruct lookahead;
destruct matched;
try rewrite -> firstn_nil in *;
try rewrite -> skipn_nil in *;
simpl in *;
try rewrite -> Nat.sub_0_r in *;
solve_assumption;
try solve [apply FrontAlign_nil];
try solve [inversion HM];
try solve [inversion HD];
try solve [discriminate HL].

simpl in *.
inversion HM; subst.
injection HL; intros.
subst.
assert (Hmain: (firstn (length lookahead) main) ++ (skipn (length lookahead) main) = main) by apply firstn_skipn.
symmetry in Hmain.
apply FrontAlign_cons; solve_assumption.
remember (length lookahead) as n.
rewrite -> H.
apply (FrontAlign_shorter _ _ Hmain H4).

-
left; intros HM.
destruct main;
destruct against;
destruct lookahead;
destruct matched;
try rewrite -> firstn_nil in *;
try rewrite -> skipn_nil in *;
simpl in *;
try rewrite -> Nat.sub_0_r in *;
solve_assumption;
try solve [apply FrontAlign_nil];
try solve [inversion HM];
try solve [inversion HD];
try solve [discriminate HL];
try solve [apply Diverge_contradicts_FrontAlign; apply Diverge_nil].
unfold not; intros HMG.
assert (Hmain: (firstn (length lookahead) main) ++ (skipn (length lookahead) main) = main) by apply firstn_skipn.

admit.

admit.

admit.


	Qed.

(*
Theorem FrontAlign_shorter:
	forall bigger smaller extension aligned,
		bigger = smaller ++ extension
		-> FrontAlign bigger aligned
		-> FrontAlign smaller aligned.
*)

	Fixpoint compute_lookahead_recursive main against lookahead :=
		match main, against with
		(* EqTotalAlign against main *)
		| [], [] => lookahead
		(* EqExtends against main *)
		| [], (_ :: _) => lookahead
		(* EqDivergesAt *)
		| (m :: _), [] => (lookahead ++ [m])
		| (m :: main'), (a :: against') => if compute_equivalent m a
			(* recursive *)
			then compute_lookahead_recursive main' against' (lookahead ++ [m])
			(* EqDivergesAt *)
			else (lookahead ++ [m])
		end.

	Definition compute_lookahead main against :=
		compute_lookahead_recursive main against [].

	(*
		main: A
		against: B
		lookahead: A
		lookahead = (firstn 1 main)
		EqDivergesAt :=
			TotalAlign (firstn 0 against) (firstn 0 lookahead)
			/\ Diverge (skipn 0 against) (skipn 0 lookahead)

		main: A B C
		against: A E
		lookahead: A B
		lookahead = (firstn 2 main)
		EqDivergesAt :=
			TotalAlign (firstn 1 against) (firstn 1 lookahead)
			/\ Diverge (skipn 1 against) (skipn 1 lookahead)

		main: A B
		against: A B C
		lookahead: A B
		lookahead = (firstn 2 main)
		EqDivergesAt :=
			TotalAlign (firstn 1 against) (firstn 1 lookahead)
			/\ Diverge (skipn 1 against) (skipn 1 lookahead)
	*)

	Inductive PredictsAgainst: list T -> list T -> list T -> Prop :=
		| PredictsAgainst_extends:
			forall lookahead main against extension n rest,
			main = lookahead ++ extension -> extension <> []
			-> against = (firstn n main) ++ rest
			-> EqualityDiverge rest main
			-> PredictsAgainst lookahead main against
		| PredictsAgainst_contained:
			forall lookahead main against extension,
			main = lookahead
			-> against = main ++ extension,
			-> PredictsAgainst lookahead main against
	.

	Theorem PredictsAgainst_predicts_accurately:
		forall lookahead main against aligned,
			PredictsAgainst lookahead main against
			-> (FrontAlign main aligned -> FrontAlign lookahead aligned)
				(FrontAlign lookahead aligned -> ~(FrontAlign against aligned))
				/\ extends against main.
	Proof.

	Qed.


	Definition predicts_against (lookahead main against: list T) :=
		forall aligned,
			FrontAlign lookahead
			FrontAlign lookahead aligned -> ~()

		forall lookahead, exists extension, main = lookahead ++ extension
			/\ ~(exists extension, ).


End Lookahead.



Section FoldsAlignment.
	Variable T U: Type.
	Variable Align: T -> list U -> Prop.

	(* definition of Foldsalign *)
	Inductive Foldsalign: list T -> list U -> Prop :=
		| Foldsalign_nil: Foldsalign (@nil T) (@nil U)
		| Foldsalign_cons: forall (t: T) (us: list U) lt lu,
			Align t us -> Foldsalign lt lu -> Foldsalign (t :: lt) (us ++ lu)
	.
	Hint Constructors Foldsalign: core.


	(* definition of FoldsMatch *)
	Inductive FoldsMatch: list T -> list U -> Prop :=
		| FoldsMatch_nil: forall lu, FoldsMatch (@nil T) lu
		| FoldsMatch_cons: forall (t: T) (us: list U) lt lu,
			Align t us -> FoldsMatch lt lu -> FoldsMatch (t :: lt) (us ++ lu)
	.
	Hint Constructors FoldsMatch: core.


End FoldsAlignment.


(*Theorem TotalAlign_transfer:
	forall T CA CB,
		(forall a b, CA a b <-> CB a b) ->
		forall lta ltb, @TotalAlign T T CA lta ltb <-> @TotalAlign T T CB lta ltb.
Proof.
split; generalize dependent ltb;
induction lta; intros ltb; induction ltb;
intros HCA; try apply TotalAlign_nil; try inversion HCA; subst;

apply TotalAlign_cons; crush.
apply H; crush.
Qed.


an interesting idea for matching: if a list extends a smaller one, then it is contradictory to say that the smaller one matches but the bigger one doesn't. this could be the crux of what it means for something to "lookahead".

Definition TokenDefinition := String.string.
Definition Token := String.string.

Definition TokenMatches (def: TokenDefinition) (token: Token): Prop := def = token.
Hint Unfold TokenMatches: core.
Definition TokenMatchesBool def token :=
	{TokenMatches def token} + {~(TokenMatches def token)}.
Obligation Tactic := crush.
Program Definition match_token def token: TokenMatchesBool def token :=
	Reduce (String.string_dec def token).

Definition TokenDefinitionsSame (a b: TokenDefinition): Prop := a = b.
Hint Unfold TokenDefinitionsSame: core.
Definition TokenDefinitionsEquivalent (a b: TokenDefinition): Prop :=
	forall token, TokenMatches a token <-> TokenMatches b token.
Hint Unfold TokenDefinitionsEquivalent: core.

Ltac token_unfold :=
	unfold TokenDefinitionsEquivalent in *;
	unfold TokenDefinitionsSame in *;
	unfold TokenMatches in *.

Theorem TokenDefinitionsSameEquivalent:
	forall a b, TokenDefinitionsSame a b <-> TokenDefinitionsEquivalent a b.
Proof. split; token_unfold; crush. Qed.
Hint Rewrite TokenDefinitionsSameEquivalent: core.


Definition TokenPath := list TokenDefinition.
Definition TokenStream := list Token.

Definition TokenPathsSame a b :=
	@TotalAlign TokenDefinition TokenDefinition TokenDefinitionsSame a b.
Hint Unfold TokenPathsSame: core.
Definition TokenPathsEquivalent a b :=
	@TotalAlign TokenDefinition TokenDefinition TokenDefinitionsEquivalent a b.
Hint Unfold TokenPathsEquivalent: core.

Ltac path_unfold :=
	unfold TokenPathsEquivalent in *;
	unfold TokenPathsSame in *;
	token_unfold.


Theorem TokenPathsSameEquivalent:
	forall a b, TokenPathsSame a b <-> TokenPathsEquivalent a b.
Proof.
	split; apply (@TotalAlign_transfer TokenDefinition TokenDefinitionsSame TokenDefinitionsEquivalent TokenDefinitionsSameEquivalent).
Qed.
Hint Rewrite TokenPathsSameEquivalent: core.

Definition PathMatchesStream path stream :=
	@TotalAlign TokenDefinition Token TokenMatches path stream /\ path <> [].
Hint Unfold PathMatchesStream: core.

		(*| [ H: TokenMatches _ _ |- _ ] =>*)
			(*token_unfold; crush*)
Ltac invert_PathMatchesStream :=
	crush; repeat match goal with
		| [ H: PathMatchesStream _ _ |- _ ] =>
			inversion H; clear H; crush
		| [ H: @TotalAlign _ _ _ _ _ |- _ ] =>
			inversion H; clear H; crush
	end.

Theorem PathMatchesStream_path_not_empty:
	forall stream, ~(PathMatchesStream [] stream).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_path_not_empty: core.

Theorem PathMatchesStream_stream_not_empty:
	forall path, ~(PathMatchesStream path []).
Proof. destruct path; invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_stream_not_empty: core.

Theorem PathMatchesStream_same_length:
	forall path stream, PathMatchesStream path stream -> length path = length stream.
Proof. intros ? ? [->%TotalAlign_same_length]; easy. Qed.

Theorem PathMatchesStream_length_non_zero:
	forall path stream, PathMatchesStream path stream -> 0 <> (length path) /\ 0 <> (length stream).
Proof. invert_PathMatchesStream. Qed.
Hint Resolve PathMatchesStream_length_non_zero: core.





Theorem PathMatchesStream_same_if_match_same_aux :
	forall path stream, PathMatchesStream path stream -> path = stream.
Proof. intros ? ? H. induction H; crush. Qed.

Theorem PathMatchesStream_same_if_match_same:
	forall a b stream,
		PathMatchesStream a stream
		-> PathMatchesStream b stream
		-> a = b.
Proof.
	intros ? ? ? ->%PathMatchesStream_same_if_match_same_aux ->%PathMatchesStream_same_if_match_same_aux.
Qed.




Definition PathSameStartAs (smaller bigger: TokenPath): Prop :=
	smaller <> [] -> bigger <> []
	-> forall stream, PathMatchesStream smaller stream -> PathMatchesStream bigger stream.
Hint Unfold PathSameStartAs: core.

Check PathSameStartAs.

Theorem PathSameStartAs_always_when_same:
	forall a b, a = b -> a <> [] -> PathSameStartAs a b.
Proof. crush. Qed.
Hint Resolve PathSameStartAs_always_when_same: core.

Theorem PathSameStartAs_if_not_then_not_same:
	forall smaller bigger, (~PathSameStartAs smaller bigger) -> smaller <> bigger.
Proof. crush. Qed.
Hint Resolve PathSameStartAs_if_not_then_not_same: core.

(*H: forall stream: TokenStream,
			PathMatchesStream
				(a :: smaller) stream ->
			PathMatchesStream [] stream*)

Theorem PathSameStartAs_B_longer_equal_A:
	forall smaller bigger,
		PathSameStartAs smaller bigger -> length smaller <= length bigger.
Proof.
	unfold PathSameStartAs in *. intros.
	induction smaller.
	- induction bigger; crush.
	- induction bigger.
		+ simpl in *.  apply (IHsmaller H).  rewrite (Nat.nle_succ_0 (length t0)).

			apply <- PathMatchesStream_path_not_empty in H.  apply Nat.nle_succ_0 in IHA.
		+
Qed.

Definition PathSubsumedBy (A B: TokenPath): Prop := PathSameStartAs A B /\ ~(PathSameStartAs B A).







Inductive BaseModifier: Set :=
	(*| Many*)
	| Maybe
	(*| MaybeMany*)
.
Definition Modifier := option BaseModifier.

Definition ModifierOptional (modifier: Modifier): Prop := modifier = Some Maybe.
Definition ModifierOptionalBool modifier :=
	{ModifierOptional modifier} + {~(ModifierOptional modifier)}.
Obligation Tactic := crush.
Program Definition Modifier_optional modifier: ModifierOptionalBool modifier :=
	match modifier with
	| Some m => match m with
		(*| Many => No*)
		| Maybe => Yes
		(*| MaybeMany => Yes*)
		end
	| None => No
	end.

Inductive Node: Type :=
	| consume (modifier: Modifier) (defs: NonEmpty TokenDefinition)
.
Definition Node_modifier (node: Node): Modifier :=
	match node with
	| consume modifier _ => modifier
	end.
Hint Unfold Node_modifier: core.

Inductive NodeMatchesStream: Node -> TokenStream -> Prop :=
	| NodeMatchesStream_consume_required: forall modifier defs stream,
		PathMatchesStream (listOf defs) stream
		-> NodeMatchesStream (consume modifier defs) stream
	| NodeMatchesStream_consume_optional: forall modifier defs,
		ModifierOptional modifier
		-> NodeMatchesStream (consume modifier defs) []
.
Hint Constructors NodeMatchesStream: core.

Theorem Node_non_optional_stream_not_empty:
	forall node stream,
		~(ModifierOptional (Node_modifier node))
		-> NodeMatchesStream node stream
		-> stream <> [].
Proof. intros n s r ma. inversion ma; crush; inversion H. Qed.
Hint Resolve Node_non_optional_stream_not_empty: core.

Theorem Node_non_optional_length_non_zero:
	forall node stream,
		~(ModifierOptional (Node_modifier node))
		-> NodeMatchesStream node stream
		-> 0 < (length stream).
Proof. intros n s r ma. inversion ma; inversion H; crush. Qed.
Hint Resolve Node_non_optional_stream_not_empty: core.

Inductive NodeListMatchesStream: list Node -> TokenStream -> Prop :=
	| NodeListMatchesStream_base: forall node stream,
		NodeMatchesStream node stream
		-> NodeListMatchesStream [node] stream
	| NodeListMatchesStream_append: forall node stream nodes streams,
		NodeMatchesStream node stream
		-> NodeListMatchesStream nodes streams
		-> NodeListMatchesStream (node :: nodes) (app stream streams)
.
Hint Constructors NodeListMatchesStream: core.

(*what's maybe more interesting here is that if you add a non-optional node to any list of nodes, the length of the match will only increase and not merely remain the same*)

Theorem Node_add_non_optional_increases_match_length:
	forall node stream nodes streams,
		~(ModifierOptional (Node_modifier node))
		-> NodeListMatchesStream (node :: nodes) (app stream streams)
		-> (length streams) < (length (stream ++ streams)).
Proof.
	intros n s ns ss r ma. inversion ma; crush. inversion H2; crush. inversion H; crush.
Qed.
*)


(*
a correct lookahead is one that, for some nodes/node lists A and B
- the lookahead head matches A
- if a token stream would match A ++ B, then the lookahead will say yes
- if a token stream would not match A ++ B (but only B?) then it will say no. probably that means that it simply *doesn't* match B??


if the lookahead matches B, then it also must *totally* match A, implying that A is subsumed by B
otherwise, it must not match B but only A
this means there are two ways to construct evidence that a lookahead is correct
- it matches A but not B
- it matches A and B, but B subsumes A

LookaheadCorrect L A B := forall stream, LookaheadYes L A B stream <-> NodeListMatches (A ++ B) stream





If the stream is:

- merely A, does the lookahead match? my first impulse is yes, although whether the *surrounding rule* will match is a much more fraught question
-

*)



(*
now it's all about how to define a "maximal" match
that's what defines a correct lookahead, it will tell us whether to take the current option in such a way that the overall match we produce will be maximal
now just what is maximal????
*)


(*

let's say we have a rule like this that we need to generate lookaheads for
what we really want to know is what lookahead do we need to test when we hit A B
a consume is all or nothing
(A B)? (A)

the lookahead has to be (A B), since merely (A) would falsely enter the ? consume if the


*)

