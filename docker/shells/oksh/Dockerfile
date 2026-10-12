ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git build-essential libncurses-dev && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN ./configure && make -j"$(nproc)" && install -D oksh /out/bin/oksh

FROM ${BASE}
RUN apt-get update && apt-get install -y --no-install-recommends libncurses6 && rm -rf /var/lib/apt/lists/*
COPY --from=build /out/bin/oksh /usr/local/bin/oksh
