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

	Theorem Equivalent_TotalAlign:
		forall lt1 lt2 lu,
			EqTotalAlign lt1 lt2
			-> (MatchTotalAlign lt1 lu <-> MatchTotalAlign lt2 lu).
	Proof.
		intros ? ? ? HEA; split; generalize dependent lu;
		induction HEA as [| t1 t2]; intros [| u] HMA;
		inversion HMA; try solve [constructor];
		specialize (equivalence_implies_match t1 t2) as [HM _];
		specialize (HM H u) as [];
		match goal with
		| HM: Match ?t u, HM': Match ?t u -> Match _ u |- _ =>
			apply HM' in HM; apply TotalAlign_cons; solve_assumption;
			apply IHHEA; assumption
		end.
	Qed.

	Theorem TotalAlign_Equivalent:
		forall lt1 lt2 lu,
			(MatchTotalAlign lt1 lu <-> MatchTotalAlign lt2 lu)
			-> EqTotalAlign lt1 lt2.
	Proof.
intros ?; induction lt1 as [| t1 lt1];
intros ?; induction lt2 as [| t2 lt2];
intros [| u lu] H; try solve [constructor];
try solve [specialize (TotalAlign_nil Match) as F; apply H in F; inversion F];
subst.
specialize (TotalAlign_nil Match) as F.
specialize (IHlt2 []) as B.
admit.
admit.

apply F in H.



intros ? ? ? [HA1 HA2].
generalize dependent lu.


induction HA1 as [| t1 ? lt1']; inversion HA2 as [| t2 ? lt2'];
try solve [constructor]; solve_crush; subst.
(*injection H6; intros; subst.*)
apply TotalAlign_cons.
apply equivalence_implies_match.
admit.


split; intros.


specialize (equivalence_implies_match t1 t2) as [_ HM].
apply HM.




	Qed.

	Theorem Equivalent_FrontAlign:
		forall lt1 lt2 lu,
			EqTotalAlign lt1 lt2
			-> (MatchFrontAlign lt1 lu <-> MatchFrontAlign lt2 lu).
	Proof.
		intros ? ? ? HEA; split; generalize dependent lu;
		induction HEA as [| t1 t2]; intros [| u] HMA;
		inversion HMA; try solve [constructor];
		specialize (equivalence_implies_match t1 t2 ) as [HM _];
		specialize (HM H u) as [];
		match goal with
		| HM: Match ?t u, HM': Match ?t u -> Match _ u |- _ =>
			apply HM' in HM; apply FrontAlign_cons; solve_assumption;
			apply IHHEA; assumption
		end.
	Qed.

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

	Ltac lookahead_matches HL :=
		try solve [rewrite -> HL; apply FrontAlign_firstn_front; assumption].

	Theorem PredictsAgainst_correct_EqTotalAlign:
		forall lookahead main against matched,
			let n := (length lookahead) in
			lookahead = (firstn n main)
			-> EqTotalAlign against main
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (MatchFrontAlign against matched -> MatchFrontAlign main matched).
	Proof.
		intros ? ? ? ? ? HL HEA; split; intros HFA; lookahead_matches HL;
		specialize (@Equivalent_FrontAlign against main matched HEA) as [H _];
		apply H; assumption.
	Qed.

	Theorem PredictsAgainst_correct_EqExtends:
		forall lookahead main against matched,
			let n := (length lookahead) in
			lookahead = (firstn n main)
			-> EqExtends against main
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (MatchFrontAlign against matched -> MatchFrontAlign main matched).
	Proof.
		intros ? ? ? ? ? HL [HA _]; split; intros HFA;
		rewrite firstn_all in *; lookahead_matches HL;
		apply (Equivalent_FrontAlign _ HA);
		apply (FrontAlign_firstn_front (length main) HFA).
	Qed.

	Theorem PredictsAgainst_correct_EqDivergesAt:
		forall lookahead main against matched,
			let n := (length lookahead) in
			lookahead = (firstn n main)
			-> EqDivergesAt against lookahead (n - 1)
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (MatchFrontAlign lookahead matched -> ~(MatchFrontAlign against matched)).
	Proof.
clear compute_equivalent; clear compute_match;
(*intros ? ? ? ? ? HL [HA HD]; split; intros HFAlm; lookahead_matches HL.*)
intros ? ? ? ? ? HL Hdiv; split; intros HFAlm; lookahead_matches HL.
intros HFAam.
apply (DivergesAt_contradicts_FrontAlign Hdiv).
destruct Hdiv as [HA HD].

specialize (Equivalent_FrontAlign matched HA) as [H1 H2].

apply (FrontAlign_skipn (n - 1)) in HFAlm.

(**)






remember (firstn (n - 1) against) as front_against;
remember (firstn (n - 1) lookahead) as front_lookahead;
remember (skipn (n - 1) against) as back_against;
remember (skipn (n - 1) lookahead) as back_lookahead.


apply DivergesAt_contradicts_FrontAlign.

(*rewrite -> HL in *.*)
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

