ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates git build-essential meson ninja-build && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN meson setup build && ninja -C build && install -D build/ksh /out/bin/loksh

FROM ${BASE}
COPY --from=build /out/bin/loksh /usr/local/bin/loksh
