ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl qemu-utils qemu-system-x86 expect openssh-client && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN mkdir -p /out && gzip -dc image.gz > image.img && rm image.gz && qemu-img convert -O qcow2 image.img disk.qcow2 && rm image.img
RUN ssh-keygen -q -t ed25519 -N '' -f /out/key && echo root > /out/user && printf '\370\003' > sercon.bin
COPY netbsd-sh/provision.exp /provision.exp
RUN expect -f /provision.exp disk.qcow2 sercon.bin "$(cat /out/key.pub)"
RUN qemu-img convert -c -O qcow2 disk.qcow2 /out/disk.qcow2

FROM ${BASE}
RUN apt-get update && apt-get install -y --no-install-recommends qemu-system-x86 openssh-client && rm -rf /var/lib/apt/lists/*
COPY vm/vmboot vm/vmsh /usr/local/bin/
COPY --from=build --chown=65534:65534 /out /vm
