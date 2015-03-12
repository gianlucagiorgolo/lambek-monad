# Introduction

Just build with Cabal:

    cabal install

# Usage

Run the theorem prover from the command line passing a lexicon as an
argument (there's a sample 'lexicon' file in the repo):

    lambek-monad lexicon

Point your browser at [http://localhost:8000](http://localhost:8000) and try to input a sequent
(the left hand side is a sentence, the right hand side is the target
formula). Ex:

    John doesnt_believe Hesperus is Phosphorus => <>s

