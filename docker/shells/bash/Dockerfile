ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential bison && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN ./configure --without-bash-malloc && make && install -D bash /out/bin/bash

FROM ${BASE}
COPY --from=build /out/bin/bash /usr/local/bin/bash
