ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git build-essential && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN ./configure --disable-lineedit --disable-nls && make -j"$(nproc)" yash && install -D yash /out/bin/yash

FROM ${BASE}
COPY --from=build /out/bin/yash /usr/local/bin/yash
