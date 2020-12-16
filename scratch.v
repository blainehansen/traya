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
