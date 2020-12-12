(*Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.*)
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List Cpdt.CpdtTactics.
Import ListNotations.

Section NonEmpty.
	Variable T: Type.
	Definition NonEmpty := { l: list T | l <> [] }.

	Obligation Tactic := crush.
	Program Definition NonEmpty_from_list(l: list T): option NonEmpty :=
		match l with
		| [] => None
		| l' => Some l'
		end.

	Lemma absurdempty: forall A, ~((@nil A) <> (@nil A)). Proof. crush. Qed.
	Definition NonEmpty_head(ne: NonEmpty): T :=
		match ne with
		| exist [] pf => match absurdempty pf with end
		| exist (hd :: tl) _ => hd
		end.

	Theorem NonEmpty_from_list_same_list:
		forall input output pf, NonEmpty_from_list input = Some (exist _ output pf)
			-> output = input.
	Proof.
		unfold NonEmpty_from_list. destruct input; crush.
	Qed.
	Hint Resolve NonEmpty_from_list_same_list: core.

End NonEmpty.


Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
