FROM haskell:9.6.7-slim
WORKDIR /still
COPY . /still
RUN ghc -threaded -O2 Main.hs -o still
RUN cp still /bin/
ENTRYPOINT ["still"]
CMD ["benchmark", "./Proofs/Auction.still", "./Proofs/Bank.still", "./Proofs/CloudServer.still", "./Proofs/Counter.still", "./Proofs/LargeMul.still"]