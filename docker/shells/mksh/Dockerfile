ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN sh Build.sh -r && install -D mksh /out/bin/mksh

FROM ${BASE}
COPY --from=build /out/bin/mksh /usr/local/bin/mksh
