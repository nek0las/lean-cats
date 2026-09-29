namespace CatSyntax

declare_syntax_cat dsl_term
declare_syntax_cat expr
declare_syntax_cat inst
declare_syntax_cat comment
declare_syntax_cat model
declare_syntax_cat assertion
declare_syntax_cat reserved
declare_syntax_cat keyword
declare_syntax_cat primitive
declare_syntax_cat name
declare_syntax_cat statement
declare_syntax_cat definition
declare_syntax_cat constraint
declare_syntax_cat annotable_events
declare_syntax_cat predefined_events
declare_syntax_cat predefined_relations
declare_syntax_cat cat_ident_part
declare_syntax_cat cat_ident
declare_syntax_cat procedure_call
declare_syntax_cat arch_spec

scoped syntax reserved:41 : expr
scoped syntax primitive : reserved
scoped syntax keyword : reserved
scoped syntax name : reserved
scoped syntax predefined_events : reserved
scoped syntax predefined_relations : reserved

scoped syntax "and" : keyword
scoped syntax "as" : keyword
scoped syntax "begin" : keyword
scoped syntax "call" : keyword
scoped syntax "do" : keyword
scoped syntax "end" : keyword
scoped syntax "enum" : keyword
scoped syntax "flag" : keyword
scoped syntax "forall" : keyword
scoped syntax "from" : keyword
scoped syntax "fun" : keyword
scoped syntax "in" : keyword
scoped syntax "let" : keyword
scoped syntax "match" : keyword
scoped syntax "procedure" : keyword
scoped syntax "rec" : keyword
scoped syntax "scopes" : keyword
scoped syntax "with" : keyword


scoped syntax "classes" : primitive
scoped syntax "linearizations" : primitive
scoped syntax "tag2events" : primitive
scoped syntax "tag2scopes" : primitive

scoped syntax assertion : keyword
scoped syntax "irreflexive" : assertion
scoped syntax "empty" : assertion
scoped syntax "acyclic" : assertion
scoped syntax "~"assertion : assertion

/- table events. -/
scoped syntax "W" : annotable_events -- write events
scoped syntax "R" : annotable_events -- read events
scoped syntax "B" : annotable_events -- branch events
scoped syntax "F" : annotable_events -- fence events
scoped syntax "RMW" : annotable_events -- read-modify-write events
scoped syntax "SRCU" : annotable_events -- srcu events
scoped syntax "IW" : annotable_events -- initial writes
scoped syntax "M" : annotable_events -- memory events, M = W ∪ R
scoped syntax "_" : annotable_events -- all events

scoped syntax annotable_events : predefined_events

/- defined_relations: -/
scoped syntax "O" : predefined_relations -- empty relation
scoped syntax "rf" : predefined_relations -- read from
scoped syntax "fr" : predefined_relations -- from read
scoped syntax "co" : predefined_relations -- from read
scoped syntax "id" : predefined_relations -- identity
scoped syntax "loc" : predefined_relations -- same location
scoped syntax "po" : predefined_relations -- program order
scoped syntax "rmw" : predefined_relations -- read-modify-write
scoped syntax "mb" : predefined_relations -- read-modify-write
scoped syntax "data" : predefined_relations -- data dependencies, starts with a read
scoped syntax "ctrl" : predefined_relations -- control dependencies, starts with a read
scoped syntax "addr" : predefined_relations -- address dependencies, starts with a read
scoped syntax "rmb" : predefined_relations -- read memory barrier, read -> read
scoped syntax "wmb" : predefined_relations -- write memory barrier, write -> write
scoped syntax "fence" : predefined_relations -- fence barrier

scoped syntax keyword : dsl_term
scoped syntax num : dsl_term
scoped syntax "(" expr ")" : dsl_term
scoped syntax cat_ident : dsl_term

scoped syntax ident : cat_ident_part
scoped syntax predefined_events : cat_ident_part
scoped syntax predefined_relations : cat_ident_part

scoped syntax ident : cat_ident
scoped syntax ident ("-" cat_ident_part)+ : cat_ident
scoped syntax predefined_events ("-" cat_ident_part)+ : cat_ident
scoped syntax predefined_relations ("-" cat_ident_part)+ : cat_ident

scoped syntax dsl_term:51 : expr

scoped syntax:51 expr:51 "|" expr:50 : expr       -- right-associative union
-- Example: a | b | c parses as a | (b | c).
scoped syntax "~" expr : expr
scoped syntax expr "&" expr : expr                -- intersection
scoped syntax:61 expr:61 ";" expr:60 : expr       -- right-associative composition
-- Example: a ; b ; c parses as a ; (b ; c).
scoped syntax expr "\\" expr : expr               -- set difference
scoped syntax:60 expr:60 "*" expr:61 : expr       -- Cartesian product
-- Example: a * b * c parses as (a * b) * c.
scoped syntax:70 expr "*" : expr                  -- Reflexive-transitive closure
scoped syntax:70 expr "+" : expr                  -- Transitive closure
scoped syntax expr "^" expr : expr
scoped syntax expr "+" expr : expr
scoped syntax expr "?" : expr
scoped syntax:71 expr "^-1" : expr
-- The procedure will return a value, so we can use it in the expression.
scoped syntax dsl_term "(" expr,* ")" : expr

scoped syntax "[" expr "]" : expr
-- Error handling in OCaml, we can just ignore it.
scoped syntax "try" expr "with" expr : expr

scoped syntax assertion expr ("as" cat_ident)? : inst
-- The flag is used to witness the assertion, so it doesn't change the states of the execution, we could just ignore it.
scoped syntax "flag" assertion expr "as" expr : inst
scoped syntax "let" cat_ident "=" expr : inst
scoped syntax "let" cat_ident "(" cat_ident,* ")" "=" expr : inst
scoped syntax "enum" cat_ident "=" sepBy(cat_ident, "||") : inst
-- event class can be R W F B RMW or a custom name like SRCU
scoped syntax "instructions" "{" annotable_events,+ "}" "[" expr "]" : inst

scoped syntax "(*" ident* "*)" : inst
scoped syntax "include" str : inst

-- Supported Architectures.
scoped syntax arch_spec : inst
scoped syntax "MIPS" : arch_spec
scoped syntax "C" : arch_spec

syntax "[model|" ident inst* "]" : command
syntax "[model|" str inst* "]" : command
syntax "[model|" inst* "]" : command
syntax (name := catexpr) "[expr|" expr "," cat_ident "," cat_ident "," cat_ident "]" : term
syntax "[keyword|" keyword "]" : term
syntax "[assertion|" assertion "]" : term
syntax (name := catinst) "[inst|" inst "," cat_ident "," cat_ident "," cat_ident "]" : command
syntax "[annotable-events|" annotable_events "," cat_ident "," cat_ident "]" : term -- Set
syntax "[predefined-events|" predefined_events "," cat_ident "," cat_ident "]" : term
syntax "[reserved|" reserved "," cat_ident "," cat_ident "]" : term
syntax "[predefined-relations|" predefined_relations "," cat_ident "," cat_ident "]" : term
syntax "[dsl-term|" dsl_term "," cat_ident "," cat_ident "," cat_ident "]" : term

end CatSyntax
