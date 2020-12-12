Add LoadPath "/home/blaine/lab/cpdtlib" as Cpdt.
Set Implicit Arguments. Set Asymmetric Patterns.
Require Import List String Cpdt.CpdtTactics.
Import ListNotations. Open Scope string_scope.

Require Import core.utils.

Inductive BaseModifier: Set :=
	| Many
	| Maybe
	| MaybeMany
.

Definition Modifier := option BaseModifier.

Definition Modifier_is_optional(modifier: Modifier): bool :=
	match modifier with
	| Some m => match m with
		| Many => false
		| Maybe => true
		| MaybeMany => true
		end
	| None => false
	end.


Definition TokenDefinition := string.
Definition Token := string.
(*Definition token_definition_precludes := string_dec.*)

Definition TokenMatchesProp (def: TokenDefinition) (token: Token): Prop := def = token.
Definition TokenMatches def token :=
	{TokenMatchesProp def token} + {~(TokenMatchesProp def token)}.

Obligation Tactic := crush.
Program Definition match_token def token: TokenMatches def token :=
	Reduce (string_dec def token).


Inductive TokensMatchProp: list TokenDefinition -> list Token -> Prop :=
	| TokensMatchProp_base:
		forall def token, TokenMatchesProp def token
			-> TokensMatchProp [def] [token]
	| TokensMatchProp_append:
		forall defs tokens def token, TokensMatchProp defs tokens -> TokenMatchesProp def token
			-> TokensMatchProp (def :: defs) (token :: tokens)
.
Hint Constructors TokensMatchProp: core.
Definition TokensMatch defs tokens :=
  {TokensMatchProp defs tokens} + {~(TokensMatchProp defs tokens)}.

(*Obligation Tactic := crush.
Program Fixpoint match_tokens defs tokens: TokensMatch defs tokens :=
	match defs, tokens with
	| def :: defs', token :: tokens' => if match_token def token
		then Reduce (match_tokens defs' tokens')
		else No
	| _, _ => No
	end.
*)

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

