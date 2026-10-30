

# LEAN4OEIS
- goal is to formalize as much formulas as possible at very low cost
- this spec does not specify everything with every detail, some decisions are left to the implementer, but its architevture should be similar to what is described in this spec

- PROPOSALS is not required to implement now, they just hint you that your architecture should later allow to add them too, you can implement it now if you consider it will be easy to add support of them rather than later

- TO_BE_CHANGED sections mention that current code does not satisfy to this spec and should be changed


- feel free to add new options(except args which is already described in this spec) to any command if you think it is useful


# Build and cache

## `lakefile.toml`

- Common Linter options should be in `lakefile.toml` instead of each generated files
- add `unusedVariables` and `style.longLine` and option with disable "definition/theorem contain sorry" warning

## Build cache — `lake exe oeis-cache`

A full `.lake/build` is far too large to rebuild per checkout, so compiled
artifacts are archived:

```
lake exe oeis-cache prune   # delete regenerable *.setup.json or other unnecessary files (the bulk of build/)
lake exe oeis-cache stat    # artifact counts and sizes by extension
lake exe oeis-cache put     # write cache/loeis-build.tar.zst + cache/manifest.json
lake exe oeis-cache get     # restore .lake/build from the archive (`lake build` should work fast after this)
```

# Database


## `sequence` — one row per OEIS sequence 

- can be created/updated by `oeis-ingest` cmd.
- should contain static data from .seq files so we do not need to re-parse them every time we want to access a sequence. 
- it should contain original text from %N %O %K %F %T %o %C lines and other information that is useful. 
- Also when last time it is updated, hash of .seq file, and status about whether it is fully completed or not (STATUS_COMPLETE all formulas/programs/comment lines are parsed and all information is extracted/formalized and Equiv/Basic files are created and verified against data points, STATUS_FORMALIZED when STATUS_COMPLETE is passed and all formulas/theorems are formally proved, STATUS_DEFINED if there is no any Equive/Basic files and only Defs and Data, STATUS_NOT_STARTED if there is no even Defs and Data files), you may also add sequence level metadata here
- rerunning the ingest script should only insert new sequences, existing rows should remain same
- also it should contain offsets of each argument determined by algorithms in Database.md file. for some sequences it is not possible to determine offsets, in that case we can leave them as null or empty(they will be filled manually or from other sources). precumputing and store this data is important because in any place of code where we need to know offsets we can just query this table instead of re-runing all the algorithms again.
- current main defintion key, key of main defintion in table of formalizations. 

## `formalization_item` - unified table of all formulas/programs/main-definitions/comments
- there should be combined table of successful or unsuccessful formalizations of formulas/programs/main definitions/comments no matter is it come from generic or template parsers or from LLM. 
- table should contain original text(exact start and end with possible new line)
- lean code(function body or theorem type without any name), this is important because we later may want to regenerate lean files with different names or code style and we should be able to regenerate them by using information from this table. 
- import package name which is needed to properly compile lean code, it can be files from OEISLib/Common, Mathlib or other OEIS sequnce Defs, formulas
- language of the original text - maindef(if text from title, note that title can contain multiple main definitions), comment(from %c section), formula(from %f section), maple, mathematica, pari, ..., and all other languages in %o section 
- for which values it is passed or failed or timed out (even if all values are correct we need to save range because later we may want to do more value checks if necessary), not that theorems can have extra universal queantifiers over unrelared extra variables, and functions can have two args 
- flag whether it is propostional defintion, computable function defintion, noncomputable function defintion(for example have same signature as main defintion of sequence but contain intermediate Real or something non computable in his body) or theorem
- there should be a field which we can store lean code of aux functions or lemmas or any other lean codes from which main formula depends
- there should be a field which we can store lean code of proof of theorem about equality of this formula with data of Data.lean file, this can be used only for main defintions, but we may swich from one main defintion to another, but proof of data equality should be kept, for other formulas it can be just empty or null, also we need to add fields for aux lemmas for data_eq. currently proof of data_eq is always filled by sorry, so we can set null all fields.
- there can be any other fields that you think is useful for to store, specific to LLM formalizations or specific to parsed formalizations
- there should be `oeis-show` cmd which shows which formulas of which sections are formalized or not, by using different colors 

## any other table can be created for any purpose, but they should work synced with each other 





## TO_BE_CHANGED
- `main_definition_hash` `formalized_formula_hashes` `unformalized_formula_hashes` `all_unformalized_formulas_text` fields of `sequence` is not needed accoriding to new Spec, if disaggree let me know
- we can combine all formula/program/main definition/comment formatization inside current `formalization_item` table(feel free to add more fields if needed), hence I guess  `formula` table is no longer needed, if disaggree let me know
- implement `oeis-show` by calling `python -m formalize show --seq` command under the hood, but currently `formalize show` only shows program sections, but should show all other sections as well

## PROPOSAL
- later we will allow `oeis-ingest` cmd to compare .seq files with current content of table and update tables with newly added formulas/programs/main definitions/comments of existing sequences and synced with other tables to  
- we still need to figure out how store proves of upper_bound and lower_bound theorems of constants, maybe in fields of `formalization_item` table where we store proof of data_eq 
- often some valid formulas get deleted because of various reasons, or a lot of ones not approved at all. they also should be formalized and we can get them from history of git repo(which started from 2024 Feb) and also from oeis [history](https://oeis.org/history?seq=A010051) pages(which have no archive and we can only get about last 100 changes for unregistered users)

# Formalization
- this doc describes how to formalize diffferent math concepts 
- static parsers, template parsers and llms should follow it

- if formula is described via generating function then lean file must contain gen_func which return PowerSeries and also formula/maindef which call .coeff against gen_func. if gen function is recursively defined then we define its recursive property and then define gen_func via axiom of choice by proving that there exists such gen_func.  


# GenExprParser

- general expression parser which will be able to parse unstructured expressions
- final terms should be human readable lean terms, do not make mess like terms, prefer macros for integral, summations or for any other short syntax if they present in lean  
- there should be intermediate ast because later we may use it to parse wolfram and latex expressions my parsing them into that ast and using same tpye inference and term construction logic and collection of built-in function. syntax which is described in this spec if called Raw syntax, later we will add Latex and Wolfram syntaxes
- architecture should be extendible because later we may want to support more complex expressions with complex syntax 
- do not use lean macro system to parse expressions because implementing parser as parser of DSL are very restrictive and less functional
- in this project we will use it to parse formula section, but parser should be general and independent from oeis project, and should not do any oeis specific handling, parser codes should be in Lean and should not depend from oeis files, it should be isolated one, but we still can list it into main lakefile.
- it is not required to strictly preserve backward compatibility, but we should try to preserve it
- it is up to you to choose whether to use Lean.Syntax to render Lean code or just create String. advantage of String is that we are more flexibe to choose how final lean code will looks like(not sure that we can choose place of parentesis in Syntax or even convert Syntax to String without altering expression or avoiding from transformations due to pretty printing)

### input text
- parser should accept raw string input. which can contain human words, unrelated chars, numbers and many unexpected things before and after math formula, so i guess we should be able find biggest valid non overlapping math expression inside given input(do not try to do some oeis specific clean up of expressions before giving them to the parser, parser should be able to find biggest valid expression automatically ignore unrelated things).
- parser should find longest valid nonoverlapping expressions inside given input and ignore unrelated words, chars. each human word can be trated as valid variable name but we should skip all of them because they can not be converted into function or proposition and most of them are just holes and should be ignored. do not create big collection of words to detect human text in order to skip them, such kind of solution is not peoper generic solution, skip them by using similar generic ways as I described 
- for now parser should not give any special meaning to "when" "if" "for" "where" words or `;` and `,` separators. current logic is sufficient to parse different parts of expression and since `,` is not valid char then it will split expression naturally in same way as any other non valid chars. `,` separator can have meaning only inside argument list of function in other places it can not be valid part of expression. 
- input expression can be interpreted in multiple ways, and parser should be able to return all possible valid interpretations which typecheck and pass verification step
- treat unicode chars as unrelated chars


### args (feel free to add any new arg in any place if it necessary) and results
- allowed_failures
- min_success_rate - minimum percentage of valid data points which should pass verification to accept formula   
- desired function names(or without name) with its offsets of arguments, acceptable types of desired function, list of computed values for various arguments(or we can pass data_eq like theorem which can be used to do simp, feel free to choose what you want)
- list of custom functions with their names, list of names of necessary lean packages, same function can have many alternatives, list of computed values
- parser also should accept user defined map of custom functions. in case oeis, OEISParser will use it to pass many alternatives definitions of Adddddd functions(currently there is many alternative for each of them with different number of arguments) and parser will start to recognize them(because oeis functions are not built-in). it can be to remove existing built function alternatives by user. note that custom function can have same name as built-in ones, so these new ones should be interpreted as alternatives too
- also note that if input expression contain few math formulas inside it them we should return few formulas and validate each of them independently. if there is chain of equalities between formulas and user want to get function type then we should create function from each equal parts. 
- parser should return exactly where all relevant parts of the formula are located without including unrelated parts,words, chars
- user can describe desired function without passing its name, but user should be able to also specify name of function(also obviously list of types which he expect to construct) and the parser should prioritize creating function with that name(there can be few definitions of same function with that name(for example equational chain), so it should return both of them as before) and if that function have holes and holes can be filled by other aux functions described in other parts of expression then that aux functions also should be consturcted(by infering its type) and then main function should be constructed by using those aux functions. if holes of desired function can not be filled then we should consider formula unparable(they should not be added into formalization_item table by OEISParser because they are not even typecheckable)
- parser also should return only necessary import packages. so parser should know which built-in functions from which package depends, custom functions also should specify their packages.
- note that I am not requireing how parser should return function defintion(even for recursive functions), as lambda or as some struct, it is up to you, to choose best one
- if user not passed name of desired function then we should return also function name in result


### types
- also parser will accept lean type of term which we expect to construct and types can be
  + Nat
  + Real
  + Int 
  + Q(Rat)
  + Complex
  + Prop
  + functions from combinations of above types like Nat→Int, Real→Real→Real.
- if type is function A→B then parser should only parse expression which starts with "func_name(arg_name1,...) = ..." (such equalities can be converted into function only if arg_name and func_name are not expression) or expression is not equality and just some "x*(x-1)" and contain only one free variable(the we should make that free variable as argument)
- if fomulas is `func_name(arg_name) = expr1 = expr2` and asked type is A->B then parser should return two functions, one for `func_name(n) = expr1` and another for `func_name(n) = expr2`
- if user asked to create Prop type and if expression is equality,inequality then we should create proposition, for chain of equalities like a1=a2=a3 we can create a1=a2/\a2=a3 by repeating smallest member of chain. or if all expressions are big then we can ceate [a1,a2,a3] list and call pairwise function of list 
- user can specify few types and parser for each new expression of input text should try to construct first asked type, if it see that it is not possible then it should try second type and so on(will be good to use type inference here too, to quickly eliminate impossible desired types).
- type inference should not be brute forced(brute forced mean that it will just create all possible combination of alternatives of all functions and then typecheck them). brute forced solution is slow and instead we should use type inference rules to find only valid alternatives of given function/operator
- type inference logic also should support automatic coercion between types, for example if function expect only Real but Nat is provided then we should inject Nat to Real convertor. narrowing types like Real to Nat,Int can be used only in top level expressions(if user want to get Nat but all interpretations return Real then we can case final expr to Nat to satisfy to the user). allowing intermediate narrowing types can be dangerously slow I guess
- after our internal type inference logic we can also construct lean string and use Lean typechecker to check is it valid or not, but we should not rely only on lean typechecker because its capabilities are limited and it does not give us enought flexibity to implement our own type inference rules 
- if many interpretations of overall formula are passing type checking, then we should prefer passing computable(`Nat.sqrt`) alternatives through verification step first then noncomputables like `Int.sqrt` then `Real.sqrt` then `Complex.sqrt`
- there should be built-in functions which parser can parse like sqrt, log, exp, sin and so on. and one function can have many alternatives, for example sqrt can be Nat.sqrt, Int.sqrt, Real.sqrt, Complex.sqrt and parser should do type inference to find only alternatives which can pass typechecking






### verification
- verification of computable function should be verified by creating in-memory env of lean and evaluating the function there(maybe using built-in eval api), without using any temporary Check files
- if it contains custom function for which we only know few data points(or we have access to data_eq like theorem which can be used to simp its values for few data points) then we can verfiy it by creating theorems and replacing other formulas with their values via simp tactic(or other techniques)
- if formula is noncomputable then we can not verify it now, but now parser should return flag indicating that this formula is noncomputable and we just need to have tests against well known valid math expressions like integrals and make sure that parser able to parse. later we may use sympy to verify them too
- if values of desired function are available then we should compute the value against all available values until for one of them timeout will be reached, 
- if current overall alternative interpretation of expression will fail for at least `allowed_failures` which will specifies how many failures are allowed for first values(continuesly they should fail starting from first member, can not be at middle), and if number of failures is less or equal than allowed then we should fix function by adding values of first few failures to the function body via `match` expression or via `if` condition. if number of failures is more than allowed then we can check whether expression contain conditions like "arg_name>constant" or not, if yes and constant is equal to number of failures then we can fix this function same way, if not then we should reject it and parser should start to validation next type valid alternatives. 
- using type inference is helping us here because validation can be heavy and checking it only against type valid alternatives will save us time. 
- in case of recursive functions we I guess elaboration step will also check whether it is terminating functions or not, if not then we should be able to check termination at least for provided values






### multiplication corner cases
- implicit multiplication can be supported for 2a exprs, not for “a b” expr because in that case consecutive words will be interpreted as muplications of variables. 
- if there is `n(n+1)/2` then we can deduce that n is variable because it added to 1 in `n+1` expr, so `n` isnot function hence `n(n+1)` should be treated as implicit multiplication. or if `a(n) = n(1+2+4)` then there we also can deduce that `n` is variable
- `(n+1)(n+2)` like expressions also should be treated as implicit multiplication
- there should be two interpretations for 2a(n) expression, one 2*a(n) and second one where 2a is function name. it is useful for hyper-geom functions like 2F1



### important corner cases to consider
- `another words (1+2*x^4)/((1-x^3)*(1-x-x^2)). - _John Doe_, Dec 29 2012`
- `a(n) = 0^n + n`. when n=0 it should return 1
- `a(n)=sum_(k=0)^n sum_(i=0)^n A002157(k,i)` - take attention to priorities, we should use finset sums here
- `g = sum{k>=1} 1/k^2` - we should use `∑'` infinite `tsum` here 
- `a(n) = a(n-1)+n^2 for n > 1` GenExprParser should return recursive function by filling missing a(0) case from provided values  
- `a(n)=2*n+n/2+n!!` division should have few alternatives like Nat.div, Int.div, Real.div, and so on. factorial can be applied few times
- `integral(x=0)^1 x^2`
- `a(n) = 3n^2 - 7*n + 6`. should be converted to fun n => 3 * (n ^ 2) + 6 - 7 * n because 3 * (n ^ 2) - 7 * n can be 0 if 3 * (n ^ 2) s small than 7*n, so we have big problem here, because fun n => 3 * n ^ 2 - 7 * n + 6 formalization works for n>=2 and llm may decide to to add special if conditions for for n=0,1 and leave base case 3 * n ^ 2 - 7 * n + 6, which will work but it is not simplest formula. so we just need to write all additions and then substructions if we dealing with Nats(same can happen with multiplication and division using NAt->Nat->Nat defintions of them, so apply them here too)
- sometimes expression can contain intermediate real number, rational and integer numbers but final result will always be Nat. for example A084847: `a(n) = 2*3^n+(n-2)*2^(2n-1)`. is hard if we want to have Nat->Nat, because of the negative intermediate values for n=0 and n=1 because we expect 1 and 4 results for them. even for Nat->Int, we have rational intermediate values for n=0 and n=1. to solve this problem we can define few alternatives for power operator for Nat,Int,Rat,Real. in this case only Rat and Real will pass validation step of GenExprParser 
- `a(n) = 3*n + (9*n mod 6 - 6)` - seems like proporities should be `3*n + ((9*n) mod 6) - 6`
- we need to be careful with priorities of `a(n) = sqrt(6*n*(3*n + (-1)^n - 3)-3*(-1)^n + 5)/sqrt(2)` too
- `res = sin(2*pi)*e` - pi and e are well known constants, in some cases pi(x) is function which return number of primes less than or equal to x. user can ask to create `Real` type from this expression and we should return `sin(2*pi)*e` in lean code and `res` name as function name(function without arg)
- `A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2` - power of function is written directly after its name
- `A046080(a(n)) = 1, A046109(a(n)) = 12. - Jean-Christophe Hervé, Dec 01 2013` - should give two seorate theorems if desired type is Prop. note that ` Jean-Christophe` is also valid math expression but it have holes, so it will be skipped
- `log_2(n)` or `log_x(2)` should be parsed as `log(2,n)` or `log(x,2)` respectively, so some functions first arguemnt can be written as subscript, and we should parse it correctly no matter what is value of first argument
- `i` can be Complex.I or it can be just variable in aggegators like summation or product
- `a(n) = |n-1|` 
- `b(n) = n^2+1; a(n) = b(b(b(n)))` - if user ask to create Nat->Nat for "a" function then we should create aux lean function `def b(n: Nat): Nat := n^2 + 1` and then return defintion of `a` using `b`
- `a = c^c + c where c=floor(3^10/2^10)` - if user ask to create Nat for "a" constant then we should create aux lean constant `def c: Nat := floor (3^10/2^10)` and then return definition of `a` using `c`



## PROPOSALS
- expressions like `a(0)=1, a(1)=2 and for general case we have a(n)=expr1`(can contain more words, extra chars, or `;` instead of `,` but as we decided earlier we should not give them any meaning and handle by special way) have computed values `a(0)=1`, `a(1)=2` and if their number no more than number of failures of `a(n)=expr1` main body(against available data points) then we should do same as we doing when inout text contain explicit `n>=2` condition.
- to support reproducibility we can create table of parser versioning and for each run of parser we can store hash of latest git commit of parser(if there is draft then we can also store patch file content against latest commit). and every formalization item should also store hash of parser which generated it, but this approach can make everything slow especially if just want to parse only one formula
- add support of limit or asymptote if user specified Prop type 
- add support of limits and convert its statement into proposition using `tendsto`
- support derivative "f'(x)" notation
- later support `a(n) = A000081(n) - (Sum_{1<=i<=j, i+j=n} A000081(i)*A000081(j)) + (1-(-1)^(n-1)) * binomial(A000081(n/2)+1,2) / 2 [Li, equation 4.2]. - Walt Rorie-Baety, Jul 05 2021`
- `a(n) = Sum_{d1|n,d2|n} mu(gcd(d1,d2))`  
- `Sum{i,0,n} Sum{i<=j<=k<=n} f(i,j,k)`(j and k is not declated in ouside so we should assume they are new agregating variables) 
- `rx = 1.23...` - should be parsed to 1.23<=x<1.24
- later we should support `EReal` type because some formulas assume that there is `oo` value so that dividing 1 by oo will give 0 
- later we might add support of this types
  + PNat
  + {n: Nat // constant_number <= n }
  + {n: Int // constant_number <= n } 
- now we should be able to verify only computable function and also function for whome values already computed, later to verify noncomputable expression(like Real) we can translate lean into sympy in order to verify
- for generating functions we might ask to PowerSeries type and they can be verified by using sympy since it is fast and free. `print([g.coeff(x, i) for i in range(10)])` and recursive generaing function can be constructed by repeatedly feeded same formula back inside g up to 10 times, `g = 0; for _ in range(10): g = sp.series(x / (1 - x * g), x, 0, 10).removeO()` 


# OEISParser
- under the hood this parser will use GenExprParser 
- GenExprParser do not know anything about OEIS, and OEISParser having access to tables, should collect all necessary information and pass it to GenExprParser
- before giving expression to GenExprParser we can clean followings(do not try to clean up expression too much, because you can not guess how expressions can looks like and your regex may clean up also important parts of expression, we we should only clean up folowings, further cleanup will do GenExprParser by finding valid parts of expression)
  + only if author name starts and ends with underscore and date is written immediately after it, like "_AlphabetCharsAndSpace_, Dec 29 2012"
  + like "From _AlphabetCharsAndSpace_, Jul 24 2016: (Start)"
  + "(End)"
- before calling underlaying GenExprParser we should recognize which sequnces are used inside expression and pass them as custom functions to GenExprParser
- desired types which it should pass to the GenExprParser: first should be native types of sequnce(ArgTypes), then signatures with Nat args types, then signatures with Int args types. to parse theorems not functions we can pass Prop type
- oeis-parser cmd should have `--allowed-failures` option and pass to GenExprParser
- formulas will be accepted only if it passes at least first 66%(this should be configurable via arguments and passed to GenExprParser) of available data points and timeout for remaining ones(if it fails in at least one of them then should be rejected)
- for now we can not validate non-computable functions so we can just reject them and do not store in `formalization_item` table yes, only computable formulas should be stored for now, no matter they failed or not
- for formula section we should prefer to specify `a` and `Adddddd` function names, or for 2d sequences `a` and `T` and `Adddddd` alternative names of desired function  

### TO_BE_CHANGED
- we can have scripts to run parser against all already parsed and validated formulas every few days and check are there any formula which we can no longer parse and validate, if so we should collect them, find issue and fix

# Generator — `lake exe oeis-gen`

- Reads `Metadata/oeis.db` and writes the per-sequence `Data.lean`, `Defs.lean`, `Equiv_<hash>.lean`, `Basic_<hash>.lean` files in OEISLib/Axxx/Axxxxxx/ dir. 
- Skeleton content is exactly the file shape specified in [OEISLib.md](OEISLib.md).
- should read `sequences` and `formalization_item` tables from database and generate all files,
- comments should contain only original text, no any other comment is needed. note .seq files can contain different comments,formulas and programs which formalization is exact same, so one formalized formula can have few original texts and we need to mention all of them in comments 
- genrator should be generic and it should not inspect lean code stored in `formalization_item` table and should not do any processing based on content of lean code, it should take that code as is and generate the necessary files accordingly, so template scripts and parsers should generate that lean code so that generator can just copy them in final files without any chnage and preprocessing(only exception can be recursive defintions)  
- lean files should use lean module system https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/

```
lake exe oeis-gen --all 
lake exe oeis-gen --bucket A000 # `--force` overwrites existing files (otherwise existing files are kept)
lake exe oeis-gen --seq A000001 
lake exe oeis-gen --hash <hash> # generate files from successfully formalized item of `formalization_item` table
```
`--force` - overwrites existing files (otherwise existing files are kept).
`--dry-run` - generates files in memory and prints them to stdout, does not write any files.

## TO_BE_CHANGED
- Currently only template parsers generate main defintions, for others Data.lean and Defs.lean files are filled with `sorry` placeholder. in case of template parsers,main defintion is determineed by llm with good quality, for others we still need to find good algorithm of main defintion determination, but filling them with sorries does not block as now.


# LLM-agent autoformalization pipeline

- for simplicity `python -m formalize` cmd can be implemented by python
- we should have `run` subcmds to start agent to formalize gaps of various sections, verify them, insert new formalizations into `formalization_item` table, and create lean files for them
- we should be able to run it by batches(by including formulas from few sequences) to make it more efficient, ability to run only against given sequnce or only given language section
- `retry` subcmd to retry failed run again by continuing from previous conversation
- `show` subcmd against session to show what llm generated for  various sequences, his notes, and what is verified or failed
- `show` subcmd against sequnce to show what which formulas of which sections are formalized or not, by using different colors 
- there should be `--anon` option by which we can ask llm to anoniize sequnces by changing their name and giving them new random names, and only sharing few values with llm, because llms can remember about which sequnce it is and can return well known formulas instead of desired formulas. also in same batch we should include only one formula from each sequence because sometimes llms can halucinate and return same lean formula for different original texts of formulas of same sequence. 
- without `--anon` we can include any number of formulas from same sequence in one batch, by sharing any information along with original text. this can be useful if final formalization will be reviewed by human 
- for each language there should be skill file which described how expressions should be translated into lean, it should contain table of each syntax/funcname and we can llok into original text and determine which syntax/funcname is used and only share relevant rows of that table
- there should be option by which we can ask llm to learn from previous mistakes and suggest new skill rows. it can be specified on first run(in this case it should formalize and then we will separatelly ask to give new skill by second request), or on retry run to update the skill file after finish of conversation


## TO_BE_CHANGED
- verification and file generation should be done in unified way for all expressions of all languages no matter source come from genparse, templates of llm autoformalization 
- now we using **blake2b-64** hash algorithm, but after unification we will use unified `hex(String.hash)` as we using it for other cases
- change `python -m formalize` to `python -m autoformalize`


## PROPOSALS 

### for multiline formula detection
- there are formulas or programs which are multiline, and there is no clear way to detect/separate them from each other
- genexpr parser can parse and extract only formulas which is inside one line, template parsers can detect multilines too because llm preprocessed instances of that sequences and found out multilines too and can detect them.
- we can look into git history or oeis [history](https://oeis.org/history?seq=A010051) pages to see which formulas are commited separately and we can assume that new ones are independent from others
- after all of this we can split formulas by using `Alternative:` or `(* Or *)` comments too
- if there is some formula which is inside one line(its mean that previous formula or next one is already formalized) and still unformalized, then we can assume that it is independent from others
- we can collect remaining unformalized formulas and ask llm to count number of formulas, if it is matching with our count then we can assume that we correctly separated
- if formula have holes and it can not be filled from other formulas of same input text then instead of throwing error we can create universally quantified theorem over that hole variable or function which accept that hole variable as argument


# OEISLib — per-sequence file shape

For each OEIS sequence `<name>` (its A-number, e.g. `A000027`) the
formalization lives in the directory `OEISLib/<bucket>/<name>/` (e.g. `OEISLib/A000/A000027/`).

Files:

- `Defs.lean` — the main definition and its standard API.
- `Data.lean` — known terms.
- `Equiv_<hash>.lean` / `Basic_<hash>.lean` — one file per
  alternative formula (hash defined below).



## Naming and type resolution
- Defs and Data declarations are inside `namespace <name>`, except the main definition
  which is at top level and is named `<name>`.
- Equiv and Basic declarations should be inside `namespace <name>_<firs_8chars_of_hash>`.
- Type abbrevs start with a capital letter: `ArgType`, `RetType`,
  `FlatArgType`, `FlatRetType`. Every other declaration — values, functions,
  theorems, and the offset constants `offset` / `flatOffset` — starts
  lowercase.
- Signatures in this document use the placeholders `ArgType`, `RetType`,
  `FlatArgType`, `FlatRetType`. In generated code these placeholders must be
  resolved to concrete Lean types, and every declaration other than the
  `abbrev` definitions themselves must state its types concretely — including
  variable binders in theorems. A generated signature must never mention an
  abbrev name.

Type resolution rules:

- **Index type of one argument**, from its start index (the smallest index
  the argument ranges over):
  - start `0` → `Nat`
  - start `1` → `PNat`
  - start `k ≥ 2` → `{n : Nat // k ≤ n}`
  - start `k < 0` → `{n : Int // k ≤ n}`

  Subtypes are allowed wherever an index type appears (including components
  of a table index).
- **ArgType.**
  - Scalar: resolved by the index rule from the sequence offset (first number
    of the `%O` line).
  - Table: `T1 × T2`, where `T1` is resolved from the start index of `n` and
    `T2` from the start index of `k` (determined per the priority table in
    §2).
  - Decimal: `Unit`.
- **RetType** — `Int` if at least one listed term is negative, otherwise
  `Nat`; for decimal sequences it is `Real`.
- **Flat view.** Tables (read row by row) and decimal constants (read digit
  by digit) also have a flat, single-index view; scalar sequences do not. It
  is resolved like a scalar sequence:
  - `FlatArgType` — from `flatOffset` by the index rule.
  - `FlatRetType` — the type of the listed values: equal to `RetType` for
    tables; `Nat` (digits) for decimal sequences.
  - `flatOffset` — the flat index of the first listed term:
    for a decimal sequence it is always `0`;
    for a table it is the product of starting indicies of first and second params.

Every total extension (`fn`, `fz`, and their flat/table analogues) returns a
junk value (`0` of the return type) on arguments outside the real domain.

## Main definition vs proposition

Applies to all three sequence shapes.

- If the title (`%N`) states a rule that can be written directly as a Lean
  function (including over `Real`), that function is the main definition:
  define `<name>` first. `prop` is defined after it, as the relation that
  characterizes the sequence (the pointwise form `prop n z := z = <name> n`
  is always acceptable); then `prop_correct` holds by `rfl`.
- Otherwise the sequence is defined propositionally: define `prop` first,
  prove (or leave as `sorry`) that exactly one value satisfies it for each
  index, and obtain `<name>` via `Classical.choice`; `prop_correct` follows
  from the construction.

## Hashes of Equiv / Basic files

The hash is computed from the **original unformalized formula text**, never
from the formalized Lean code:

- `formulaHash(text) = hex(String.hash text)` — Lean core `String.hash`,
  rendered as 16 lowercase hexadecimal digits
  (`Scripts/OeisIngest/Parse.lean`).
- The hashed text is exactly the fragment of the source that the
  parser/template recognizes as the formula (its matched snippet).
  Surrounding human-language prose, author names and comments are skipped. 
  if it is multiline formula then hash should be generated from all lines along with '\n'
- if exact same formula of `Equiv` appears in many languages for same sequence, 
  then only one Equiv file should be generated and hash should be generated from concatenation of all formulas with '\n' separator.

## Alternative definitions and property theorems (`Equiv_<hash>.lean` / `Basic_<hash>.lean`)

Common to all three sequence shapes.

An `Equiv_<hash>.lean` file contains one alternative **full** definition of
the sequence, named `formula`, together with `theorem formula_eq`, in
exactly one of the two following forms:

1. **Value form.** `formula` has the exact signature of one of defs/props (no matter flat or not) in the main
   in `Defs.lean` (like .fn, .flat, ,prop ... or one of the other defs or props), and `formula_eq` states pointwise
   equality of formula with that declaration
2. **Proposition form.** `formula` has the signature of `prop` (or
   `flatProp`): `formula : ArgType → RetType → Prop` (flat:
   `FlatArgType → FlatRetType → Prop`), and `formula_eq` states logical
   equivalence for all parameters:
   `formula_eq (n : ArgType) (z : RetType) : formula n z ↔ prop n z`
   (flat analogue: `formula n z ↔ flatProp n z`).

Mathematics shared between members of a family is placed in `OEISLib/Common` and
called from the generated file, not duplicated per sequence.

Every unproved theorem in an `Equiv` or `Basic` file can be closed with `sorry`
**only after** a check (`interval_cases`, or `decide`/`norm_num` where
applicable) that the statement holds for every index covered by the data;
the check must fail — and thereby reject the formula — if any data point
contradicts it.

A formula that states a property but does **not** fully determine the
sequence produces a `Basic_<hash>.lean` file: theorems only, no
`def formula`, in other words we should place here statements about properties of that sequence, 
and property should not totally define that sequence(other wise we should define it in `Equiv_<hash>.lean`)

## 1. Simple scalar sequences

Sequences whose terms are `Nat`/`Int` valued and which have exactly one index
argument — i.e. neither `tabl`/`tabf` nor `cons`.

### Defs.lean
- `abbrev ArgType`, `abbrev RetType` (resolved by the rules above), and
  `abbrev offset : Int`.
- `def <name> : ArgType → RetType` — the main definition, per the
  main-definition rule above.
- `def prop : ArgType → RetType → Prop` — the defining relation.
- `def fn : Nat → RetType` — total extension to `Nat`: agrees with
  `<name>` on arguments that correspond to an in-domain index, junk `0`
  otherwise. Omitted when `offset < 0` (when `ArgType` is an `Int` subtype).
  this is needed in some cases where we want to compose `a(b(...))` sequences and `b` return Nat 
  while main def of `a` accept PNat, in this case we can call `a.fn` 
- `def fz : Int → RetType` — total extension to `Int`: agrees with
  `<name>` on in-domain indices, junk `0` otherwise. Always present.
  Any formula that references another sequence may call that sequence's
  `fz` or `fn` if types are not compatible.
- `theorem prop_correct (n : ArgType) : prop n (<name> n)`.
- Coherence: `theorem fn_eq` (`fn` agrees with `<name>` under the domain
  hypothesis), `theorem fz_eq` (`fz` agrees with `<name>` under the domain
  hypothesis), `theorem fn_eq_fz` (`fn` and `fz` agree on their overlapping
  domain). To keep these proofs cheap, define `fn` and, where possible,
  `<name>` itself in terms of `fz`.

### Data.lean
- `def data : List RetType` — all terms OEIS provides, in order:
  `data[i]` is the term at OEIS index `offset + i`.
- `@[simp] theorem data_eq` relates `<name>` to `data` on the data range;
  `theorem data_eq_fn` and `theorem data_eq_fz` relate `fn` and `fz` to
  `data`, and are proved from `data_eq`. Each theorem carries a bound
  hypothesis restricting the index to the data range; the list position is
  the argument index minus `offset`.
- Proofs can use `decide` / `interval_cases`. For non-computable sequences,
  prove one lemma per value and combine them in `data_eq`.

## 2. Table sequences (`tabl`)

Two-argument sequences `T(n,k)`.

**`tabf` sequences are skipped for now.** Their offsets, their dimension,
and their structure are not known; they are not formalized until that is
figured out.

### Start indices of n and k

Determined in this priority order; the first source that answers a
question wins:

| Priority | Source | What it gives |
| --- | --- | --- |
| 1 | `%O` line, first number | start index of **n** |
| 2 | Name text such as `0 <= k <= n` or `1 <= k <= n` | start index of **k** (also the end index of k) |
| 3 | Formula such as `T(n,0) = ...` or `T(n,1) = ...` | start index of **k** |
| 4 | Code such as `for n=0.. for k=0..n` or `n=1.. k=1..n` | start indices of both **n** and **k** |
| 5 | Guess: **k** starts at the same index as **n** | used only if nothing else says |

### Defs.lean
- `abbrev ArgType := T1 × T2` — pair of the index types of `n` and `k`,
  each resolved from its own start index by the index rule; either
  component may itself be a subtype (e.g. `PNat × {n : Nat // 2 ≤ n}`).
  `abbrev RetType`, `abbrev offset : Int` (the start index of `n`),
  `abbrev flatOffset : Int := 0`.
- `def <name> : T1 → T2 → RetType` — the main two-argument definition.
- `def fn : Nat → Nat → RetType` — total, all arguments `Nat`, junk `0`
  outside the domain; omitted when either component of `ArgType` is an
  `Int` subtype.
- `def fz : Int → Int → RetType` — total, all arguments `Int`, junk `0`
  outside the domain; always present; used for composition.
- `def prop : T1 → T2 → RetType → Prop`, `theorem prop_correct`, and
  coherence theorems relating `fn` and `fz` to the main definition.
- Flat (row-by-row reading order) API, in `namespace <name>`:
  `abbrev FlatArgType`, `abbrev FlatRetType` (equal to `RetType`),
  `def flat : FlatArgType → FlatRetType`,
  `def flatFn : Nat → FlatRetType`,
  `def flatFz : Int → FlatRetType`,
  `def flatProp : FlatArgType → FlatRetType → Prop`,
  and theorems `flat_prop_correct`, `flat_fn_eq`, `flat_fz_eq`,
  `flat_fn_eq_fz` — the flat analogues of the scalar coherence theorems.
- A bridge theorem states that, under the row-major bijection between flat
  positions and index pairs in the table domain, `flat` at that position
  equals `<name>` applied to that pair.

### Data.lean
- `def flatData : List FlatRetType` — the terms in OEIS listing order;
  theorems `flat_data_eq`, `flat_data_eq_fn`, `flat_data_eq_fz`, each with
  a bound hypothesis restricting the flat index to the data range. 
  Also `date_eq` /`data_eq_fn` / `data_eq_fz` for the two-argument view, proved two be equal to data from flatData.


## 3. Decimal-number sequences (`cons`)

Sequences whose keyword list (`%K`) contains `cons`: the sequence is one
real constant, and the listed terms are the digits of its decimal
expansion.

### Defs.lean
- `abbrev ArgType := Unit` (`()`), `abbrev RetType := Real`.
- `def <name> : Real` — the constant itself.
- the index-based API lives on the flat digit view:
  `abbrev flatOffset : Int := 0` always 0 
  `abbrev FlatArgType := Nat`,
  `abbrev FlatRetType := Nat`,
  `def flat : Nat → Nat` (digit at the given position),
  `def flatFz : Int → Nat` (junk `0` outside the domain),
  `def flatProp : Nat → Nat → Prop` (if hard to define flat, then we can define a prop and use it to define flat),
  and theorems `flat_prop_correct`, `flat_fn_eq`, `flat_fz_eq`,
  `flat_fn_eq_fz`.
- A bridge theorem states that for every digit position in the domain,
  `flat` at that position equals the corresponding digit of the decimal
  expansion of `<name>`.

### Data.lean
- `def flatData : List Nat` — the digits in listing order; theorems
  `flat_data_eq`, `flat_data_eq_fn`, `flat_data_eq_fz`, each with a bound
  hypothesis restricting the flat index to the data range.
- `theorem upper_bound: <name> < 1.23456790` - an upper bound with real value of digits available in `flatData`, plus 1 to the last digit
- `theorem lower_bound: 1.23456789 <= <name>` - a lower bound with real value of digits available in `flatData`




## TO_BE_CHANGED
- we should move current OEISLib files to OEISLib/Common,rename OEISLib to OEISLib and update all imports accordingly 
- avoid from importing `Mathlib.Tactic` in Defs and Data files if all defs and theorems are filled by sorry


# Templates — `lake exe oeis-template`

A template formalizes a *family* of sequences (same math shape, different
constants) in one module. The generic runner provides all common machinery;
the template provides only family logic. Authoring guide: `TEMPLATES.md`.

```
lake exe oeis-template <template> --all
lake exe oeis-template <template> --bucket A147
lake exe oeis-template <template> --seq A147999 [--seq ...] [--force] [--dry-run]
```
`--dry-run` parrses/validate and generates files in memory and prints them to stdout, does not write any files or change any table.

- template runner should have nonrestrictive common args to not require new templates to satisfy many requirements, common things should be done in template runner, and template should only focus on family specific logic.
- underlying template can have custom args and unknown args passed through to the template should be propagated to the underlying template.
- we should find templates by analyzing sequences via static scripts (which finds patterns where only constants or small expressions differ) or by loading them into llm context and asking llm to find patterns. final table of currently found templates should be stored in text file or in db and after implementing it we should mark template as completed in that table

Per sequence a template:

1. llm can read .seq files to determine collection patterns
2. write code which check which formulas/comments/programs/maindefs are matching which collection of patterns and insert their formalizations into `formalization_item` table
3. writen code should not read .seq files because it is slow, instead it should read the `sequence` table and maybe other tables to be fast
4. optionally we can ask template to also use function of `oeis-gen` to generate `Data.lean`, `Defs.lean`, `Equiv_<hash>.lean`, `Basic_<hash>.lean` files for each sequence in the family. this will guarantee that all generated files ill have standard shape. but by default templates should not create lean files, they only need to write into `formalization_item` table.





# Verification

- there should be `oeis-veify` cmd which will accept sequence(s) or hash of fomulas in `formalization_item` table and verify them against data with specified range of values and update table accordingly
- it should also have `--dry-run` option to just print the result of verification without updating the table 
- to make things faster there can be batch mode where we will import all formulas imports at same time in same lean env and then verify them all at once in same env
- there should be filter options by which we can say formulas with which status should be verified
- to make batch verification easy useful we can add new options in generic formula parser or llm autoformalizer to not verify formulas and just insert them into `formalization_item` with corresoping status, and then we can run `oeis-verify` cmd to verify them all at once
- we should reuse verification logic of GenExprParser 





## TO_BE_CHANGED
- remove Check/ files and all that logic, instead we should insert rows into `formalization_item` table and then call `oeis-verify` cmd, to have unified way of verification
- other tools which is written in lean can call functions of `oeis-verify` instead of invoking `oeis-verify` cmd




