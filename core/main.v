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

	Theorem Equivalent_FrontAlign:
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

	Definition PredictsAgainst lookahead main against :=
		exists common divergent,
		lookahead = common ++ divergent
		/\ lookahead = firstn (length lookahead) main
		/\ (
			(EqDivergesAt lookahead against (length common))
			\/ EqExtends against main
			\/ EqTotalAlign against main
		).

	Definition PredictsAgainst_consequences :=
		forall lookahead main against matched,
			PredictsAgainst lookahead main against
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (
					(MatchFrontAlign lookahead matched -> ~(MatchFrontAlign against matched))
					\/ (MatchFrontAlign against matched -> MatchFrontAlign main matched)
				).
	  .

		(*
			there are three cases for a main/against:
			1. they are exactly equivalent: EqTotalAlign against main
			2. against extends main: EqExtends against main (lookahead = main)
			3. main extends against: EqExtends main against (EqDivergesAt lookahead against)
			4. they have a point of divergence: (EqDivergesAt lookahead against)

			the definition of DivergesAt makes 3 and 4 equivalent, but they have different consequences regarding prediction
			in 4, if lookahead (and therefore main) matches, then by construction against can't match since the tail of against doesn't align
			but in 3, it instead means that main (and lookahead!) is itself a lookahead for against

			or perhaps this is our situation for an inferred unless!!!
			in situation 3, merely testing for *main* to match could erroneously cause us to move forward and parse a shorter sequence when the longer sequence could match, so rather than emitting a mere lookahead for main, we emit a *negative* lookahead for against (and a minimal lookahead to test if we should enter main)
		*)

	(*Definition PredictsAgainst lookahead main against :=
		let n := (length lookahead) in
		lookahead = (firstn n main)
		/\ (
			(0 < n /\ EqDivergesAt lookahead against (n - 1))
			\/ EqExtends against main
			\/ EqTotalAlign against main
		).*)

	Ltac lookahead_matches HL :=
		try solve [rewrite -> HL; apply FrontAlign_firstn_front; assumption].

	Theorem PredictsAgainst_correct_EqTotalAlign:
		forall lookahead main against matched,
			lookahead = (firstn (length lookahead) main)
			-> EqTotalAlign against main
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (MatchFrontAlign against matched -> MatchFrontAlign main matched).
	Proof.
		intros ? ? ? ? HL HEA; split; intros HFA; lookahead_matches HL;
		specialize (@Equivalent_FrontAlign against main matched HEA) as [H _];
		apply H; assumption.
	Qed.

	Theorem PredictsAgainst_correct_EqExtends:
		forall lookahead main against matched,
			lookahead = (firstn (length lookahead) main)
			-> EqExtends against main
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (MatchFrontAlign against matched -> MatchFrontAlign main matched).
	Proof.
		intros ? ? ? ? HL [HA _]; split; intros HFA;
		rewrite firstn_all in *; lookahead_matches HL;
		apply (Equivalent_FrontAlign _ HA);
		apply (FrontAlign_firstn_front (length main) HFA).
	Qed.

	Theorem PredictsAgainst_correct_EqDivergesAt:
		forall lookahead main against matched,
			(
				exists common divergent,
				lookahead = common ++ divergent
				/\ lookahead = firstn (length lookahead) main
				/\ (EqDivergesAt lookahead against (length common))
			)
			-> (MatchFrontAlign main matched -> MatchFrontAlign lookahead matched)
				/\ (
					(MatchFrontAlign lookahead matched -> ~(MatchFrontAlign against matched))
					\/ (MatchFrontAlign against matched -> MatchFrontAlign main matched)
				).
	Proof.
intros ? ? ? ? [common [divergent [HLCD [HL [HTA HD]]]]];
split; lookahead_matches HL.

rewrite -> HLCD in HTA;
rewrite -> HLCD in HD;
rewrite -> skipn_length_append in *;
rewrite -> firstn_length_append in *.
destruct common as [| c common'];
destruct divergent as [| d divergent'];
destruct against as [| a against'];
rewrite_trivial_firstn_skipn;
try rewrite -> app_nil_l in *;
try solve [inversion HD];
try solve [inversion HTA].




left; intros HFAlm; intros HFAam;
rewrite -> HLCD in *.
inversion HFAlm; inversion HFAam; crush.



destruct (skipn (length common) against) as [| a against'].
rewrite -> HLCD in HFAlm.
inversion HD; inversion HFAlm; inversion HFAam; crush.

destruct divergent as [| d divergent'];
try solve [inversion HD].




(*intros ? ?; generalize dependent lookahead;
induction main as [| m main']; intros ? ? ? ? HL Hn [HTA HD];*)

intros ? ? ? ? ? HL Hn [HTA HD];
split; lookahead_matches HL.
destruct main as [| m main'];
destruct against as [| a against'];
destruct matched as [| u lu];
destruct lookahead as [| l lookahead'];
try solve [right; intros; constructor];
try solve [subst n; simpl in Hn; inversion Hn];
try solve [right; intros H; inversion H].
rewrite_trivial_firstn_skipn.

inversion HTA;
simpl in n; subst n; simpl in *; rewrite -> Nat.sub_0_r in *;
subst_injection HL;
specialize (firstn_nil_cases _ _ H0) as [Hblah | Hblah];
try solve [discriminate Hblah];
rewrite -> Hblah in *; rewrite_trivial_firstn_skipn;
left; intros; inversion H1.

inversion HTA;
simpl in n; subst n; simpl in *; rewrite -> Nat.sub_0_r in *;
subst_injection HL;
try solve [rewrite_trivial_firstn_skipn; inversion H0];
specialize (firstn_nil_cases _ _ H0) as [Hblah | Hblah];
try solve [discriminate Hblah];
rewrite -> Hblah in *; rewrite_trivial_firstn_skipn.
admit.

inversion HD;
simpl in n; subst n; simpl in *; rewrite -> Nat.sub_0_r in *;
subst_injection HL.
right; intros HFAam.
inversion HTA; inversion HFAam; subst.

specialize (firstn_nil_cases _ _ H3) as [Hblah | Hblah];
solve_crush;
rewrite -> Hblah in *; do 2 rewrite_trivial_firstn_skipn; subst;
discriminate H.


rewrite -> Nat.sub_0_r in *;
rewrite_trivial_firstn_skipn.
admit.

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
		intros ? ? ? ? [HL [[Hn H] | [H | H]]];
		try solve [
			specialize (
				PredictsAgainst_correct_EqDivergesAt main matched HL Hn H
			) as HF; split; first [apply HF | left; apply HF]
		];
		try solve [
			specialize (PredictsAgainst_correct_EqExtends matched HL H) as HF;
			split; first [apply HF | right; apply HF]
		];
		try solve [
			specialize (PredictsAgainst_correct_EqTotalAlign matched HL H) as HF;
			split; first [apply HF | right; apply HF]
		].
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
split; simpl in *;
try solve [rewrite -> HL; reflexivity];
try solve [right; right; constructor];
try solve [
	right; left;
	unfold EqExtends; unfold Extends; unfold DivergesAt;
	rewrite_trivial_firstn_skipn; split; constructor
].
-
left.

specialize (IHmain [] [a]).
simpl in IHmain.

apply IHmain.

right; left.


left; split; rewrite -> HL; simpl; constructor.
rewrite_trivial_firstn_skipn; constructor.
rewrite_trivial_firstn_skipn.


try solve [; constructor].



split.

		Qed.


	Theorem compute_lookahead_recursive_correct:
		forall main against before_look lookahead,
			lookahead = compute_lookahead_recursive main against before_look
			-> length before_look <= length main
			-> PredictsAgainst lookahead main against.
	Proof.
intros ? ? ? ? HC HL; split.
destruct main as [| m main']; destruct against as [| a against'];
unfold compute_lookahead_recursive in HC; rewrite_trivial_firstn_skipn.
destruct before_look; crush.
destruct before_look; crush.
destruct before_look; simpl in *; subst; simpl in *.
reflexivity.

admit.
simpl in *.
destruct (compute_equivalent m a).



split.


	Qed.

	Definition compute_lookahead main against :=
		compute_lookahead_recursive main against [].

	Theorem compute_lookahead_correct:
		forall main against lookahead,
			main <> [] -> against <> []
			-> lookahead = compute_lookahead main against
			-> PredictsAgainst lookahead main against.
	Proof.
intros ?; induction main as [| m main'];
intros ? ? Hmain Hagainst Hlookahead;
destruct against as [| a against'];
try contradiction.
unfold PredictsAgainst; unfold compute_lookahead in Hlookahead;
clear Hmain; clear Hagainst; split.
-
unfold compute_lookahead_recursive in Hlookahead.
destruct (compute_equivalent m a).
+
simpl.


+


-


	Qed.

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

End Lookahead.


(*Theorem DivergesAt_Transfer:
		forall n lookahead against matched,
			MatchFrontAlign lookahead matched
			-> MatchFrontAlign against matched
			-> n < length lookahead
			-> ~(EqDivergesAt lookahead against n).
	Proof.
intros ?; induction n; intros ? ?.

intros ? HFAlm HFAam HL [HTA HD];
do 2 rewrite -> skipn_O in *; do 2 rewrite -> firstn_O in *;
inversion HD.

inversion HFAlm; inversion HFAam; solve_crush; subst.
clear HL.
injection H3; intros; subst; clear H3.

injection H8; injection H4; injection H9; intros; subst;
clear H8; clear H4; clear H9; rename t into t1; rename u into t2; rename u0 into u; rename lt into lt1; rename lu into lt2; rename lu0 into lu.

rewrite <- H0 in HL; simpl in HL; inversion HL.

specialize (match_requires_equivalance H6 H2) as HE.
apply H in HE; assumption.

intros ? HFAlm HFAam HL [HTA HD].
inversion HFAlm; inversion HFAam; solve_crush; subst.
try solve [inversion HD].
injection H6; intros; subst; clear H6.
simpl in *.
rename lt into lookahead.
rename lt0 into against.
rename lu into matched.
apply lt_S_n in HL.
apply (IHn lookahead against matched); solve_assumption.
unfold EqDivergesAt; unfold DivergesAt; split; solve_assumption.
inversion HTA; solve_assumption.
	Qed.*)



(*Theorem Equivalent_TotalAlign:
	forall lt1 lt2,
		EqTotalAlign lt1 lt2
		-> (forall lu, MatchTotalAlign lt1 lu <-> MatchTotalAlign lt2 lu).
Proof.
	intros ? ? HEA; split; generalize dependent lu;
	induction HEA as [| t1 t2]; intros [| u] HMA;
	inversion HMA; try solve [constructor];
	specialize (equivalence_implies_match t1 t2) as [HM _];
	specialize (HM H u) as [];
	match goal with
	| M: Match ?t1 u, H: Match ?t1 u -> Match ?t2 u
	|- MatchTotalAlign (?t2 :: _) _ =>
		specialize (H M) as ?; apply TotalAlign_cons; solve_assumption;
		apply IHHEA; assumption
	end.
Qed.
Theorem TotalAlign_Equivalent:
	forall lu lt1 lt2,
		MatchTotalAlign lt1 lu
		-> MatchTotalAlign lt2 lu
		-> EqTotalAlign lt1 lt2.
Proof.
	intros ?; induction lu as [| u]; intros ? ? HE1 HE2;
	inversion HE1; inversion HE2;
	try solve [constructor]; try solve [discriminate];
	subst; apply TotalAlign_cons;
	try match goal with
	| M1: Match ?t1 u, M2: Match ?t2 u |- _ =>
		apply (match_requires_equivalance M1 M2)
	end;
	apply IHlu; assumption.
Qed.*)



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

