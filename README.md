# propositional-calculus

Compile theorems written with deduction into a full (most likely very tedious) proof from only axioms and existing theorems

You write deduction in a file, making sure to quote the correct theorem and axioms. Currently A1, A2, A3, and self implication are built in, and you will need to supply the proof for other theorems. Then you can write out your proof in a proof file in the following format

```
name the_name_of_theorem

import dependent_proof

var A
var B
var any_other_variable

assume some_assumption ==> name_of_formula

|- formula [reason] ==> name_of_formula
```

For `the_name_of_theorem`, name it anything with alphanumeric characters and underscore (`_`).
For `dependent_proof`, put the name of the file, without the `.txt` extension, so the parser can find it. But when you use the theorem, use the name of the theorem as declared in the proof file.
For `some_assumption`, simply write out the formula you want to assume. You can assign that line a variable and quote it later
There are two things following the turnstile (`|-`). First, the formula, second is reason. There are two valid reason
```
modus_ponens line1 line2
```
where `line1` is `A -> B` and `line2` is `A`. Or
```
apply some_theorem(A, B, ...)
```
which means you use `some_theorem` with the positional variables `A, B, ...`

Then you can run `python3 main.py file_name.txt` for the proof

See the `examples` folder for some examples, e.g. `python3 main.py examples/contradiction_part1.txt`


# Under construction 🚧
- Checking the correctness of proof. Currently if you give it wrong proof, it will just regurgitate the wrong proof back
- Reduce the number of output lines. It sometimes still proves the same statement that is proven before.
- Ability to expand the proof
- Emit better error message, possibly including traceback.
- Multiple theorems in the same file
- Comment in file
- Check that all the variables are declared
