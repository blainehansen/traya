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
	Definition list_extends bigger smaller :=
		exists extension: list T, extension <> [] /\ bigger = smaller ++ extension.
	Hint Unfold list_extends: core.

	Theorem TotalAlign_extends_longer:
		forall bigger smaller, list_extends bigger smaller
			-> length smaller < length bigger.
	Proof.
		intros ? ? [extension []]; subst;
		induction smaller; destruct extension; crush.
	Qed.

	Theorem TotalAlign_extends_aligns_longer:
		forall bigger smaller smaller_align bigger_align,
			list_extends bigger smaller
			-> TotalAlign smaller smaller_align
			-> TotalAlign bigger bigger_align
			-> length smaller_align < length bigger_align.
	Proof.
		intros ? ? ? ? extends HS HB;
		rewrite <- (TotalAlign_same_length HS);
		rewrite <- (TotalAlign_same_length HB);
		apply TotalAlign_extends_longer; exact extends.
	Qed.

	Theorem FrontAlign_extends:
		forall bigger smaller aligned,
			list_extends bigger smaller
			-> FrontAlign bigger aligned
			-> FrontAlign smaller aligned.
	Proof.
		intros ? ? ? [extension [_ HB]] HM;
		apply (FrontAlign_shorter _ _ HB HM).
	Qed.



	Definition TotalAlign_contains bigger smaller :=
		(forall lu, TotalAlign smaller lu -> TotalAlign bigger lu)
		/\ exists lu, TotalAlign bigger lu /\ ~(TotalAlign smaller lu).
	Hint Unfold TotalAlign_contains: core.

	Theorem TotalAlign_extends_equivalent_contains:
		forall smaller bigger,
			list_extends smaller bigger <-> TotalAlign_contains smaller bigger.
	Proof.
		unfold list_extends in *; unfold TotalAlign_contains in *.
split.

-
intros [extension []].
subst.
split.
	Qed.*)





(*Theorem ListsMatch_portion_ListsCorrespond:
	forall lt lu,
		ListsMatch lt lu
		-> exists lu_corr lu_ext,
			lu = lu_corr ++ lu_ext /\ ListsCorrespond lt lu_corr.
Proof.
	intros ? ? HM;
	exists (firstn (length lt) lu); exists (skipn (length lt) lu); split;
	try solve [symmetry; apply (firstn_skipn (length lt) lu)];
	induction HM; crush.
Qed.*)



(*|
	HL: length ?lt_one = length ?lu_one,
	HC: ListsCorrespond (?lt_one ++ ?lt_two) (?lu_one ++ ?lu_two)
|- _ =>
	let F := fresh "F" in
	assert (F: length lt_two = length lu_two)
		by apply (ListsCorrespond_split_lengths lt_one lu_one lt_two lu_two HC), HL;
	solve [discriminate F]
|
	HL: length ?lt_two = length ?lu_two,
	HC: ListsCorrespond (?lt_one ++ ?lt_two) (?lu_one ++ ?lu_two)
|- _ =>
	let F := fresh "F" in
	assert (F: length lt_two = length lu_two)
		by apply (ListsCorrespond_split_lengths lt_one lu_one lt_two lu_two HC), HL;
	solve [discriminate F]*)



(*
Fixpoint ListsCorrespondComp {T U: Type} (C: T -> U -> Prop) (lt: list T) (lu: list U): Prop :=
	match lt, lu with
	| [], [] => True
	(*| [t], [u] => C t u*)
	| (t :: lt'), (u :: lu') => C t u /\ ListsCorrespondComp C lt' lu'
	| _, _ => False
	end.
Hint Unfold ListsCorrespondComp: core.

Theorem ListsCorrespond_equivalent:
	forall T U C lt lu, @ListsCorrespond T U C lt lu <-> @ListsCorrespondComp T U C lt lu.
Proof.
	split;
	generalize dependent lu;
	induction lt; intros lu H; induction lu; inversion H; crush.
Qed.
Hint Rewrite ListsCorrespond_equivalent: core.
*)





(*Theorem PathMatchesStream_hnmn:
	forall path stream, path <> [] -> ~(PathMatchesStream path stream -> PathMatchesStream [] stream).
Proof.
	intros . unfold not in *. intros. apply H.  invert_PathMatchesStream.
Qed.*)

(*Theorem PathSameStartAs_nothing_smaller_than_empty:
	forall smaller, ~(PathSameStartAs smaller []).
Proof.
	intros. unfold not, PathSameStartAs. intros. apply (PathMatchesStream_hnmn H). destruct smaller.
- crush.
-  intros.
Qed.*)

(*Theorem PathSameStartAs_path_not_empty:
	forall path, ~(PathSameStartAs [] path).
Proof.
	intros. unfold PathSameStartAs. unfold not. intros.
	destruct path.
- destruct stream.
	+
	+ apply PathMatchesStream_path_not_empty with (stream := stream). apply H.
-

	apply PathMatchesStream_path_not_empty with (stream := stream). apply H.

	destruct path.
- apply PathMatchesStream_path_not_empty with (stream := []). apply H. contradiction.
- apply PathMatchesStream_path_not_empty with (stream := stream). apply H0.

Qed.*)

(*Theorem matching_streams_never_match_against_empty:
	forall A stream, A <> [] -> ~(PathMatchesStream A stream -> PathMatchesStream [] stream).
Proof.
	intros. unfold not. intros. destruct A.
	- contradiction.
	- apply PathMatchesStream_path_not_empty in H0. contradiction.  crush.
	intros A. induction A.
	- intros. unfold not. intros. crush. rewrite <- PathMatchesStream_path_not_empty.
	-
Qed.*)


























Definition ModifierMany (modifier: Modifier): Prop := modifier = Some Many /\ modifier = Some MaybeMany.
Definition ModifierManyBool :=
	{ModifierMany modifier} + {~(ModifierMany modifier)}.
Obligation Tactic := crush.
Program Definition Modifier_many modifier: ModifierManyBool modifier :=
	match modifier with
	| Some m => match m with
		| Many => Yes
		| Maybe => No
		| MaybeMany => Yes
		end
	| None => No
	end.


(*
| ConsumeMatchesStream_many_consume: forall modifier defs stream,
		ModifierMany modifier
		-> PathMatchesStream (listOf defs) stream
		-> ConsumeMatchesStream (consume modifier defs) (app stream stream)
*)






Inductive PathMatches: TokenPath -> TokenStream -> TokenStream -> Prop :=
	| PathMatches_base: forall def token,
		TokenMatchesProp def token
		-> forall remainder, PathMatches [def] (token :: remainder) [token]
	| PathMatches_append: forall def token,
		TokenMatchesProp def token
		-> forall path stream remainder, PathMatches path (stream ++ remainder)%list stream
		-> PathMatches (def :: path) (token :: (stream ++ remainder)%list) (token :: stream)
.
Hint Constructors PathMatches: core.

(*Inductive PathMatchesFront: TokenPath -> TokenStream -> TokenStream -> Prop :=
	| PathMatchesFront_all: forall path stream,
		PathMatches path stream
		-> forall remainder, PathMatchesFront path (stream ++ remainder) stream
.*)


Inductive Node: Type :=
	| Consume (modifier: Modifier) (defs: NonEmpty TokenDefinition)
	(*| Or (modifier: Modifier) (choices: NonLone (NonEmpty Node))*)
	(*| Subrule (modifier: Modifier) (rule_name: string)*)
	(*| MacroCall (modifier: Modifier) (macro_name: string) (args: NonEmpty (NonEmpty Node))*)
	(*| Var (modifier: Modifier) (arg_name: string)*)
	(*| LockingVar (modifier: Modifier) (locking_arg_name: string)*)
	(*| Paren (modifier: BaseModifier) (nodes: NonLone Node)*)
.

(*Inductive GrammarItem: Type :=
	| TokenDef (name: string)
	| Rule (name: string) (definition: NonEmpty Node) (locking_args: list LockingArg)
	| Macro (name: string) (args: NonEmpty Arg) (definition: NonEmpty Node) (locking_args: list LockingArg)
	| VirtualLexerUsage (name path: string) (args: Regex?) (exposed_tokens: list string)
.*)

(*Fixpoint compute_lookahead (target against: TokenPath): Lookahead target against := .*)



(*
Inductive TokensMatchProp: list TokenDefinition -> list Token -> Prop :=
	| TokensMatchProp_base:
		forall def token, TokenMatchesProp def token
			-> TokensMatchProp [def] [token]
	| TokensMatchProp_append: forall defs tokens def token,
		TokensMatchProp defs tokens
		-> TokenMatchesProp def token
			-> TokensMatchProp (def :: defs) (token :: tokens)
.
Hint Constructors TokensMatchProp: core.
Definition TokensMatch defs tokens :=
	{TokensMatchProp defs tokens} + {~(TokensMatchProp defs tokens)}.
*)

(*
Theorem TokensMatchProp_same_not_empty:
	forall defs tokens, TokensMatchProp defs tokens -> defs <> [] /\ tokens <> [].
Proof.
	intros d t m. induction m; crush.
Qed.
Hint Resolve TokensMatchProp_same_not_empty: core.
Theorem TokenMatchesProp_not_if_empty:
	forall defs tokens, defs = [] \/ tokens = [] -> ~(TokensMatchProp defs tokens).
Proof.
	intros d t [dn|tn] m; induction m; crush.
Qed.
Hint Resolve TokenMatchesProp_not_if_empty: core.
*)

(*
Definition match_tokens: forall defs tokens, TokensMatch defs tokens.
	refine (fix match_tokens_recursive defs tokens: TokensMatch defs tokens :=
		match defs, tokens with
		| [def], [token] => Reduce (match_token def token)
		| def :: defs', token :: tokens' => if match_token def token
			then Reduce (match_tokens_recursive defs' tokens')
			else No
		| _, _ => No
		end
	); try (apply TokensMatchProp_base; crush); try (intros m; inversion m; crush).
	-
Defined.


Record Consume: Type := consume {
	tokens: NonEmpty TokenDefinition,
}.
*)
