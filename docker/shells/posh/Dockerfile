ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential xz-utils autoconf automake && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN autoreconf -fi && ./configure && make -j"$(nproc)" && install -D posh /out/bin/posh

FROM ${BASE}
COPY --from=build /out/bin/posh /usr/local/bin/posh
