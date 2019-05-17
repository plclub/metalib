# Coq (official?) images, see https://github.com/coq-community/docker-coq/wiki
FROM coqorg/coq:${coq_version}

# Adding metalib and ott through opam
RUN opam update -y                                                     \
 && opam repo -y add coq-extra-dev https://coq.inria.fr/opam/extra-dev \
 && opam install -y coq-metalib ott

