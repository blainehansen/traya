Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require String.
Require Import Cpdt.CpdtTactics.
Require Import PeanoNat Lt.

Require Import core.utils.
Require Import core.alignment.


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
	Variable match_requires_equivalance:
		forall t1 t2 u, Match t1 u -> Match t2 u -> Equivalent t1 t2.

	Theorem Equivalent_reflexive:
		forall t1 t2, Equivalent t1 t2 -> Equivalent t2 t1.
	Proof.
		intros;
		specialize (equivalence_implies_match t1 t2) as forward;
		specialize (equivalence_implies_match t2 t1) as back;
		apply back; split; apply forward; assumption.
	Qed.

	(*
		It seems to me we don't really want this concept of Equivalence, but instead we would like to have optimizations that simplify any matching sequence to an optimal form, and we prove that the optimal form is perfectly equivalent to the original in all cases.

		This might be harder though, since we have to leave *no remaining optimizations* in order to demonstrate that two matching sequences are equivalent iff they are equal.
	*)
	Notation EqDiverge := (Diverge Equivalent).
	Notation EqDivergesAt := (DivergesAt Equivalent).
	Notation EqExtends := (Extends Equivalent).
	Notation EqSomeAlignment := (SomeAlignment Equivalent).
	Notation EqTotalAlign := (TotalAlign Equivalent).
	Notation EqFrontAlign := (FrontAlign Equivalent).

	Notation MatchDiverge := (Diverge Match).
	Notation MatchDivergesAt := (DivergesAt Match).
	Notation MatchExtends := (Extends Match).
	Notation MatchSomeAlignment := (SomeAlignment Match).
	Notation MatchTotalAlign := (TotalAlign Match).
	Notation MatchFrontAlign := (FrontAlign Match).

	Theorem EqTotalAlign_MatchFrontAlign:
		forall lt1 lt2 lu,
			EqTotalAlign lt1 lt2
			-> (MatchFrontAlign lt1 lu <-> MatchFrontAlign lt2 lu).
	Proof.
		intros ? ? ? HEA; split; generalize dependent lu;
		induction HEA as [| t1 t2]; intros [| u] HMA;
		inversion HMA; try solve [constructor];
		specialize (equivalence_implies_match t1 t2) as [HM _];
		specialize (HM H u) as [];
		match goal with
		| HM: Match ?t u, HM': Match ?t u -> Match _ u |- _ =>
			apply HM' in HM; apply FrontAlign_cons; solve_assumption;
			apply IHHEA; assumption
		end.
	Qed.

	Theorem EqExtends_MatchFrontAlign:
		forall main against matched,
			EqExtends against main
			-> (MatchFrontAlign against matched -> MatchFrontAlign main matched).
	Proof.
		intros ? ? ? [HA _] HFA; rewrite firstn_all in *;
		apply (EqTotalAlign_MatchFrontAlign _ HA);
		apply (FrontAlign_firstn_front (length main) HFA).
	Qed.

	Theorem EqDivergesAt_MatchFrontAlign:
		forall lookahead main common divergent rest against matched,
			lookahead = common ++ divergent
			-> main = lookahead ++ rest
			-> EqDivergesAt lookahead against (length common)
			-> (
				(MatchFrontAlign lookahead matched -> ~(MatchFrontAlign against matched))
				\/ (MatchFrontAlign main matched -> MatchFrontAlign against matched)
			).
	Proof.
intros ? ? ? ? ? ? ? Hlookahead Hmain [Halign Hdiv].
rewrite -> Hlookahead in Halign; rewrite -> Hlookahead in Hdiv;
rewrite -> skipn_length_append in *; rewrite -> firstn_length_append in *.

inversion Hdiv as [d divergent' | d a divergent' against'].
-
right; intros Hmainmatch.
clear Hdiv.
specialize (firstn_skipn (length common) against) as Hagainst.
rewrite <- H0 in Hagainst; rewrite -> app_nil_r in Hagainst; clear H0.
rewrite -> Hagainst in *; clear Hagainst.
apply (EqTotalAlign_MatchFrontAlign matched Halign).
apply (FrontAlign_firstn_front (length common)) in Hmainmatch.
subst.
remember (d :: divergent') as divergent; clear Heqdivergent.
rewrite <- app_assoc in Hmainmatch.
rewrite -> firstn_length_append in Hmainmatch.
assumption.
-
left; intros Hlookaheadmatch Hagainstmatch.

apply (FrontAlign_skipn (length common)) in Hlookaheadmatch;
rewrite -> Hlookahead in Hlookaheadmatch;
rewrite -> skipn_length_append in *.

apply (FrontAlign_skipn (length common)) in Hagainstmatch.
rewrite <- H1 in *.
rewrite <- H0 in *.
inversion Hlookaheadmatch; inversion Hagainstmatch; subst.
rewrite <- H9 in H4; clear H9; subst_injection H4.
remember (skipn (length common) matched) as matched'.
apply H.
apply (match_requires_equivalance H5 H10).
	Qed.

	Definition PredictsAgainst lookahead main against :=
		exists common divergent rest,
		lookahead = common ++ divergent
		/\ main = lookahead ++ rest
		/\ (
			(EqDivergesAt lookahead against (length common))
			\/ EqExtends against main
			\/ EqTotalAlign against main
		).

	Theorem PredictsAgainst_correct:
		forall lookahead main against matched,
			PredictsAgainst lookahead main against
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (
					(MatchFrontAlign lookahead matched -> ~(MatchFrontAlign against matched))
					\/ (MatchFrontAlign main matched -> MatchFrontAlign against matched)
					\/ (MatchFrontAlign against matched -> MatchFrontAlign main matched)
				).
	Proof.
		intros ? ? ? ? [common [divergent [rest [Hlookahead [Hmain H]]]]]; split;
		try solve [apply (FrontAlign_extension lookahead rest Hmain)];
		destruct H as [Hdiv | [Hext | Halign]];
		try specialize (
			EqDivergesAt_MatchFrontAlign _ _ _ matched Hlookahead Hmain Hdiv
		) as HF;
		try specialize (@EqExtends_MatchFrontAlign _ _ matched Hext) as HF;
		try specialize (EqTotalAlign_MatchFrontAlign matched Halign) as HF;
		crush.
	Qed.


	Fixpoint compute_lookahead main against :=
		match main, against with
		(* EqTotalAlign against main *)
		| [], [] => []
		(* EqExtends against main *)
		| [], (_ :: _) => []
		(* EqDivergesAt lookahead against (n - 1) *)
		| (m :: _), [] => [m]
		| (m :: main'), (a :: against') => if compute_equivalent m a
			(* recursive *)
			then m :: compute_lookahead main' against'
			(* EqDivergesAt *)
			else [m]
		end.

		Theorem compute_lookahead_correct:
			forall main against lookahead,
				lookahead = compute_lookahead main against
				-> PredictsAgainst lookahead main against.
		Proof.
intros ?; induction main as [| m main'];
intros ? ? HL; destruct against as [| a against'];
unfold PredictsAgainst; simpl in *; subst.

exists []; exists []; exists []; split; split;
try solve [right; right; constructor]; crush.

exists []; exists []; exists []; split; split;
try solve [
	right; left; unfold EqExtends; unfold DivergesAt;
	simpl; split; constructor
]; crush.

exists []; exists [m]; exists main';
simpl in *; split; split;
try solve [left; repeat constructor]; crush.

destruct (compute_equivalent m a); simpl in *.

remember (compute_lookahead main' against') as lookahead';
specialize (IHmain' against' lookahead' Heqlookahead')
	as [common' [divergent' [rest' [Hlookahead [Hmain [Hdiv | [Hext | Halign]]]]]]].
-
destruct Hdiv as [Halign Hdiv].
clear Heqlookahead'.
subst.
rewrite -> firstn_length_append in *.
rewrite -> skipn_length_append in *.
exists (m :: common'); exists divergent'; exists rest';
simpl in *; split; split; solve_crush.
left.
constructor; simpl.
constructor; solve_assumption.
rewrite -> firstn_length_append.
assumption.

rewrite -> skipn_length_append.
assumption.

-
destruct Hext as [Halign Hdiv].
clear Heqlookahead'.
rewrite -> skipn_all in *.
rewrite -> firstn_all in *.
exists (m :: common'); exists divergent'; exists rest';
split; rewrite -> Hlookahead; crush.
remember (common' ++ divergent' ++ rest') as main'.
right; left.
constructor; simpl in *.
constructor; solve_assumption.
apply Equivalent_reflexive; assumption.
rewrite -> firstn_all; assumption.
rewrite -> skipn_all; assumption.

-
clear Heqlookahead'.
exists (m :: common'); exists divergent'; exists rest';
split; rewrite -> Hlookahead; crush.
remember (common' ++ divergent' ++ rest') as main'.
right; right; simpl in *.
constructor; solve_assumption.
apply Equivalent_reflexive; assumption.

-
exists []; exists [m]; exists main'; simpl in *; split; split;
try solve [
	left; repeat (simpl; constructor);
	assumption
]; crush.

		Qed.

End Lookahead.
