# This is the guidance for AI tools on how to add a new instruction to LeanCats framework.

All the functionalities for parsing the cat files are in the CatParser directory.
The Syntax is used to add new architecture identifications, suppose you want to add the architecure called `MIPS`, you need to put the `MIPS` under the syntax catogary `arch_spec`.

Then in each cat file, at the begenning the cat file may has the arhicteucture specifiction, for example, in one file that has the MIPS, which means we need to import the definitions of the MIPS.

The LeanCat itself has the core part, and also the std part, 
1. For the core part, there are only a limited set of events and relations as the pritmitive types in the LeanCats, which means sometimes we need to add more instruction semantics like this.

2. For std part, the LeanCats use simple definitions instead of using the complex macros beacuse of type safety and easy to use.

we seperate the variables in different ways
1. primitity types (cores), for example what we defined in the syntax, these can be parsed by LeanCats directly.
2. Standard libaries, some types like the coe or rfe, these are defined in the std, we can find them easily.
3. The Architecture specific ones, these are enriched by the semantics of each architecture, even thuogh they have the same name, for example, the miops and riscv, they both has SYNC, but the semantics depend on each architecture deifnitions.
4. Parse errores or unkonwne variables.

So your role is working on the 3.
