ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git build-essential && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN bin/package make && install -D arch/*/bin/ksh /out/bin/ksh

FROM ${BASE}
COPY --from=build /out/bin/ksh /usr/local/bin/ksh
