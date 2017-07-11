FROM ysli/vellvm
RUN . ~/.profile \
 && opam install ott \
 && sudo apt-get install -y cabal-install gcc \
 && git clone https://github.com/plclub/lngen.git \
 && cabal update \
 && cabal install lngen/ \
 && git clone https://github.com/plclub/metalib.git \
 && make -C metalib/Metalib -j install
ENV PATH $PATH:~/.cabal/bin
