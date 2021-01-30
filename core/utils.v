Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List Cpdt.CpdtTactics.
Import ListNotations.
Require Import PeanoNat.

Notation "!" := (False_rect _ _).
Notation "[ e ]" := (exist _ e _).

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Ltac notHyp P :=
	match goal with
	| [ _ : P |- _ ] => fail 1
	| _ =>
		match P with
		| ?P1 /\ ?P2 => first [notHyp P1 | notHyp P2 | fail 2]
		| _ => idtac
		end
	end.

Ltac solve_crush := try solve [crush].
Ltac solve_assumption := try solve [assumption].
Ltac subst_injection H :=
	injection H; intros; subst; clear H.

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

Theorem firstn_cons_nil:
	forall (T: Type) n (a: T) l l', a :: l' = firstn n l -> l <> [].
Proof.
	intros; destruct l; rewrite_trivial_firstn_skipn; crush.
Qed.

Theorem skipn_cons_nil:
	forall (T: Type) n (a: T) l l', a :: l' = skipn n l -> l <> [].
Proof.
	intros; destruct l; rewrite_trivial_firstn_skipn; crush.
Qed.

Theorem firstn_length_cons:
	forall (T: Type) l (a: T),
		0 < length l
		-> firstn (length l) (a :: l) = a :: (firstn (length l - 1) l).
Proof.
	intros; destruct l; simpl in *;
	try solve [inversion H]; rewrite -> Nat.sub_0_r; reflexivity.
Qed.

Theorem firstn_nil_cases:
	forall (T: Type) n (l: list T), [] = firstn n l
		-> n = 0 \/ l = [].
Proof.
	intros ? [] []; crush.
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

Theorem contrapositive: forall P Q: Prop,
	(P -> Q) -> (~Q -> ~P).
Proof. crush. Qed.


Section NonEmpty.
	Variable T: Type.
	Definition NonEmpty := {l: list T | l <> []}.
	Definition listOf (ne: NonEmpty) := proj1_sig ne.

	Obligation Tactic := crush.
	Program Definition NonEmpty_from_list (l: list T): option NonEmpty :=
		match l with
		| [] => None
		| l' => Some l'
		end.

	Lemma absurdempty: forall A, ~((@nil A) <> (@nil A)). Proof. crush. Qed.
	Definition NonEmpty_head (ne: NonEmpty): T :=
		match ne with
		| exist [] pf => match absurdempty pf with end
		| exist (hd :: tl) _ => hd
		end.

	Theorem NonEmpty_from_list_same_list:
		forall input output pf,
			NonEmpty_from_list input = Some (exist _ output pf)
			-> output = input.
	Proof.
		unfold NonEmpty_from_list. destruct input; crush.
	Qed.
	Hint Resolve NonEmpty_from_list_same_list: core.

	Definition SafeIndex (l: list T) := {n: nat | n < length l}.
	(*Theorem SafeIndex_nth:
		forall l (i: SafeIndex l), nth_error l (proj1_sig i) = Some _.
	Proof. Qed.*)

	(*Definition safe_nth: forall (l: list T) n, n < length l -> {t: T | In t l}.
		simple refine (fix f (l: list T) (n: nat) :=
			match l, n with
			| t :: _, 0 => fun _ => [t]
			|  _ :: l', S n' => fun _ =>
				let found := (f l' n' _) in [proj1_sig found]
			| [], _ => fun _ => !
			end
		);
		solve_crush; right; apply (proj2_sig found).
	Defined.*)

	Definition safe_nth: forall (l: list T) n, n < length l -> T.
		intros l; induction l; intros n; induction n; solve_crush.
	Defined.

	Definition safe_nth_in: forall (l: list T) n, n < length l -> {t: T | In t l}.
		intros l; induction l; intros n; induction n; intros; solve_crush;
		apply (@exist _ _ a (or_introl (eq_refl a))).
	Defined.

	(*Lemma absurdsmaller: forall n, ~(n < 0). Proof. crush. Qed.
	Definition safe_index_nth: forall (l: list T) (n: SafeIndex l), T.
		simple refine (fix f l n := match l, n with
		| t :: _, exist 0 _ => t
		| _ :: l', exist (S n') _ => safe_nth l' [n']
		| [], exist _ pf => match (absurdsmaller pf) with end
		end); solve_crush.
	Fixpoint safe_index_nth (l: list T) (n: SafeIndex l) {struct n}: T :=
		match l, n with
		| t :: _, exist 0 _ => t
		| _ :: l', exist (S n') _ => safe_nth l' n'
		| [], exist _ pf => match (absurdsmaller pf) with end
		end.*)

End NonEmpty.
