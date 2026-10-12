ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential bzip2 && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN make defconfig && sed -i 's/^# CONFIG_STATIC is not set/CONFIG_STATIC=y/' .config && make -j"$(nproc)" && install -D busybox /out/bin/busybox

FROM ${BASE}
COPY --from=build /out/bin/busybox /usr/local/bin/busybox
