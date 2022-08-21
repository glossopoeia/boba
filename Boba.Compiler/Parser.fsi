// Signature file for parser generated by fsyacc
module Parser
type token = 
  | IS
  | ONE
  | TRUE
  | FALSE
  | NOT
  | TUPLE
  | LIST
  | ITERATOR
  | STRING_KEY
  | VECTOR
  | SLICE
  | DICTIONARY
  | CASE
  | FOR
  | IN
  | BREAK
  | FINAL
  | FILL
  | LENGTH
  | RESULT
  | IF
  | WHEN
  | SWITCH
  | WHILE
  | THEN
  | ELSE
  | DO
  | MATCH
  | INJECT
  | WITH
  | AFTER
  | HANDLE
  | NURSERY
  | CANCELLABLE
  | UNTAG
  | BY
  | PER
  | TRUST
  | DISTRUST
  | AUDIT
  | WITH_STATE
  | PERMISSION
  | FUNCTION
  | NATIVE
  | LOCAL
  | LET
  | BOOLEAN
  | ABELIAN
  | SYNTACTIC
  | IS_ROUGHLY
  | IS_NOT
  | SATISFIES
  | VIOLATES
  | TEST
  | LAW
  | EXHAUSTIVE
  | SYNONYM
  | TAG
  | EFFECT
  | OVERLOAD
  | INSTANCE
  | RULE
  | CLASS
  | CHECK
  | PATTERN
  | RECURSIVE
  | KIND
  | DATA
  | ABOUT
  | MAIN
  | EXPORT
  | FROM
  | AS
  | IMPORT
  | REF
  | UNDERSCORE
  | EQUALS
  | ELLIPSIS
  | DOUBLE_AMP
  | DOUBLE_BAR
  | BAR
  | DOT
  | PLUS
  | MINUS
  | STAR
  | COLON
  | DOUBLE_COLON
  | CARET
  | COMMA
  | SEMICOLON
  | FN_CTOR
  | FN_ARROW_BACK
  | FN_ARROW_FRONT
  | FN_DIVIDE
  | L_CONE
  | R_CONE
  | L_BOX
  | R_BOX
  | L_PUMPKIN
  | R_PUMPKIN
  | L_BANANA
  | R_BANANA
  | L_BIND
  | R_BIND
  | L_STAR
  | R_STAR
  | L_ARROW
  | R_ARROW
  | L_BRACKET
  | R_BRACKET
  | L_BRACE
  | R_BRACE
  | L_PAREN
  | R_PAREN
  | DOCUMENTATION_LINE of (DocumentationLine)
  | NATIVE_CODE_LINE of (NativeCodeLine)
  | CHARACTER of (CharacterLiteral)
  | STRING of (StringLiteral)
  | DECIMAL of (DecimalLiteral)
  | INTEGER of (IntegerLiteral)
  | TEST_NAME of (Name)
  | PREDICATE_NAME of (Name)
  | OPERATOR_NAME of (Name)
  | BIG_NAME of (Name)
  | SMALL_NAME of (Name)
  | EOF
type tokenId = 
    | TOKEN_IS
    | TOKEN_ONE
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_NOT
    | TOKEN_TUPLE
    | TOKEN_LIST
    | TOKEN_ITERATOR
    | TOKEN_STRING_KEY
    | TOKEN_VECTOR
    | TOKEN_SLICE
    | TOKEN_DICTIONARY
    | TOKEN_CASE
    | TOKEN_FOR
    | TOKEN_IN
    | TOKEN_BREAK
    | TOKEN_FINAL
    | TOKEN_FILL
    | TOKEN_LENGTH
    | TOKEN_RESULT
    | TOKEN_IF
    | TOKEN_WHEN
    | TOKEN_SWITCH
    | TOKEN_WHILE
    | TOKEN_THEN
    | TOKEN_ELSE
    | TOKEN_DO
    | TOKEN_MATCH
    | TOKEN_INJECT
    | TOKEN_WITH
    | TOKEN_AFTER
    | TOKEN_HANDLE
    | TOKEN_NURSERY
    | TOKEN_CANCELLABLE
    | TOKEN_UNTAG
    | TOKEN_BY
    | TOKEN_PER
    | TOKEN_TRUST
    | TOKEN_DISTRUST
    | TOKEN_AUDIT
    | TOKEN_WITH_STATE
    | TOKEN_PERMISSION
    | TOKEN_FUNCTION
    | TOKEN_NATIVE
    | TOKEN_LOCAL
    | TOKEN_LET
    | TOKEN_BOOLEAN
    | TOKEN_ABELIAN
    | TOKEN_SYNTACTIC
    | TOKEN_IS_ROUGHLY
    | TOKEN_IS_NOT
    | TOKEN_SATISFIES
    | TOKEN_VIOLATES
    | TOKEN_TEST
    | TOKEN_LAW
    | TOKEN_EXHAUSTIVE
    | TOKEN_SYNONYM
    | TOKEN_TAG
    | TOKEN_EFFECT
    | TOKEN_OVERLOAD
    | TOKEN_INSTANCE
    | TOKEN_RULE
    | TOKEN_CLASS
    | TOKEN_CHECK
    | TOKEN_PATTERN
    | TOKEN_RECURSIVE
    | TOKEN_KIND
    | TOKEN_DATA
    | TOKEN_ABOUT
    | TOKEN_MAIN
    | TOKEN_EXPORT
    | TOKEN_FROM
    | TOKEN_AS
    | TOKEN_IMPORT
    | TOKEN_REF
    | TOKEN_UNDERSCORE
    | TOKEN_EQUALS
    | TOKEN_ELLIPSIS
    | TOKEN_DOUBLE_AMP
    | TOKEN_DOUBLE_BAR
    | TOKEN_BAR
    | TOKEN_DOT
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_STAR
    | TOKEN_COLON
    | TOKEN_DOUBLE_COLON
    | TOKEN_CARET
    | TOKEN_COMMA
    | TOKEN_SEMICOLON
    | TOKEN_FN_CTOR
    | TOKEN_FN_ARROW_BACK
    | TOKEN_FN_ARROW_FRONT
    | TOKEN_FN_DIVIDE
    | TOKEN_L_CONE
    | TOKEN_R_CONE
    | TOKEN_L_BOX
    | TOKEN_R_BOX
    | TOKEN_L_PUMPKIN
    | TOKEN_R_PUMPKIN
    | TOKEN_L_BANANA
    | TOKEN_R_BANANA
    | TOKEN_L_BIND
    | TOKEN_R_BIND
    | TOKEN_L_STAR
    | TOKEN_R_STAR
    | TOKEN_L_ARROW
    | TOKEN_R_ARROW
    | TOKEN_L_BRACKET
    | TOKEN_R_BRACKET
    | TOKEN_L_BRACE
    | TOKEN_R_BRACE
    | TOKEN_L_PAREN
    | TOKEN_R_PAREN
    | TOKEN_DOCUMENTATION_LINE
    | TOKEN_NATIVE_CODE_LINE
    | TOKEN_CHARACTER
    | TOKEN_STRING
    | TOKEN_DECIMAL
    | TOKEN_INTEGER
    | TOKEN_TEST_NAME
    | TOKEN_PREDICATE_NAME
    | TOKEN_OPERATOR_NAME
    | TOKEN_BIG_NAME
    | TOKEN_SMALL_NAME
    | TOKEN_EOF
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startunit
    | NONTERM_unit
    | NONTERM_import_list
    | NONTERM_decl_list
    | NONTERM_main
    | NONTERM_import
    | NONTERM_import_path
    | NONTERM_remote
    | NONTERM_export
    | NONTERM_brace_names
    | NONTERM_name_list
    | NONTERM_name
    | NONTERM_declaration
    | NONTERM_documentation
    | NONTERM_documentation_lines
    | NONTERM_function
    | NONTERM_function_list
    | NONTERM_native
    | NONTERM_native_code_list
    | NONTERM_userkind
    | NONTERM_kind_unify
    | NONTERM_datatype
    | NONTERM_type_param_list
    | NONTERM_datatype_list
    | NONTERM_constructor
    | NONTERM_constructor_list
    | NONTERM_rule
    | NONTERM_class
    | NONTERM_overload
    | NONTERM_opt_type_param_list
    | NONTERM_instance
    | NONTERM_effect
    | NONTERM_handler_template_list
    | NONTERM_handler_template
    | NONTERM_test
    | NONTERM_law
    | NONTERM_law_param_list
    | NONTERM_law_param
    | NONTERM_test_all
    | NONTERM_check
    | NONTERM_tag
    | NONTERM_base_kind
    | NONTERM_compound_kind
    | NONTERM_constraint_list
    | NONTERM_constraint
    | NONTERM_predicate_list
    | NONTERM_predicate
    | NONTERM_qual_fn_type
    | NONTERM_base_type
    | NONTERM_val_type
    | NONTERM_top_fn_type
    | NONTERM_fn_type
    | NONTERM_fn_type_seq
    | NONTERM_fn_row_type
    | NONTERM_field_row_type
    | NONTERM_field_type
    | NONTERM_compound_type
    | NONTERM_and_sequence
    | NONTERM_or_sequence
    | NONTERM_mul_sequence
    | NONTERM_type_arg_list
    | NONTERM_term_statement_block
    | NONTERM_term_statement_list
    | NONTERM_term_statement
    | NONTERM_non_empty_simple_expr
    | NONTERM_simple_expr
    | NONTERM_word
    | NONTERM_permission
    | NONTERM_nursery_word
    | NONTERM_cancellable_word
    | NONTERM_handle_word
    | NONTERM_handler
    | NONTERM_return
    | NONTERM_param_list
    | NONTERM_handler_list
    | NONTERM_inject_word
    | NONTERM_eff_list
    | NONTERM_match_word
    | NONTERM_match_clause_list
    | NONTERM_match_clause
    | NONTERM_if_word
    | NONTERM_switch_word
    | NONTERM_switch_clause_list
    | NONTERM_when_word
    | NONTERM_while_word
    | NONTERM_for_word
    | NONTERM_for_results
    | NONTERM_for_result
    | NONTERM_for_sequence
    | NONTERM_parallel_sequences
    | NONTERM_fold_inits
    | NONTERM_function_literal
    | NONTERM_lit_expr_list
    | NONTERM_tuple_literal
    | NONTERM_list_literal
    | NONTERM_record_literal
    | NONTERM_variant_literal
    | NONTERM_case_word
    | NONTERM_case_clause_list
    | NONTERM_case_clause
    | NONTERM_field_list
    | NONTERM_field
    | NONTERM_identifier
    | NONTERM_type_identifier
    | NONTERM_pred_identifier
    | NONTERM_qualified_name
    | NONTERM_qualified_ctor
    | NONTERM_qualified_pred
    | NONTERM_no_dot_pattern_expr_list
    | NONTERM_var_only_pattern_list
    | NONTERM_pattern_expr_list
    | NONTERM_field_pattern_list
    | NONTERM_pattern_expr
    | NONTERM_tuple_pattern
    | NONTERM_list_pattern
    | NONTERM_vector_pattern
    | NONTERM_slice_pattern
    | NONTERM_record_pattern
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val unit : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> ( Unit ) 
