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
