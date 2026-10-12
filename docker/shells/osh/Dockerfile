ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN ./configure && _build/oils.sh && install -D _bin/cxx-opt-sh/oils-for-unix /out/bin/oils-for-unix

FROM ${BASE}
COPY --from=build /out/bin/oils-for-unix /usr/local/bin/oils-for-unix
RUN ln -s oils-for-unix /usr/local/bin/osh
