FROM coqorg/coq:dev
ENV OPAMYES true
RUN opam update && opam install \
    ott \
 && sudo apt-get update && sudo apt-get install -y \
    haskell-stack \
    netbase \
    ssh \
 && git clone https://github.com/plclub/lngen.git \
 && cd lngen && stack setup && stack install \
 && echo "PATH+=:$(stack path --local-bin)" >> ~/.profile
