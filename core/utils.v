Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List Cpdt.CpdtTactics.
Import ListNotations.

Notation "!" := (False_rect _ _).
Notation "[ e ]" := (exist _ e _).

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Ltac solve_crush := try solve [crush].

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
