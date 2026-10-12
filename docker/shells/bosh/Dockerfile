ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git build-essential && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN cd psmake && sh MAKE-all
RUN for d in inc libschily libxtermcap libfind libgetopt libshedit sh; do (cd "$d" && ../psmake/smake) || exit 1; done && install -D sh/OBJ/*/sh /out/bin/bosh

FROM ${BASE}
COPY --from=build /out/bin/bosh /usr/local/bin/bosh
