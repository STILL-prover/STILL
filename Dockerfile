FROM haskell:9.6.7-slim
WORKDIR /still
COPY . /still
RUN ghc -threaded -O2 Main.hs -o still
ENTRYPOINT ["still"]
CMD ["benchmark", "./Proofs/*.still"]