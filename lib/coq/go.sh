opam switch 4.09.1
eval $(opam env)
PATH=~/versions/coq-8.12/coq/bin:$PATH
make _CoqProject
make

