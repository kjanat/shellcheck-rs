ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl xz-utils qemu-utils genisoimage openssh-client && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN mkdir -p /out && xz -dc image.xz > image.qcow2 && rm image.xz && qemu-img convert -c -O qcow2 image.qcow2 /out/disk.qcow2 && rm image.qcow2
RUN ssh-keygen -q -t ed25519 -N '' -f /out/key && echo validity > /out/user \
	&& printf '#cloud-config\nusers:\n  - name: validity\n    shell: /bin/sh\n    lock_passwd: true\n    ssh_authorized_keys:\n      - %s\n' "$(cat /out/key.pub)" > user-data \
	&& printf 'instance-id: validity\nlocal-hostname: freebsd\n' > meta-data \
	&& genisoimage -quiet -output /out/seed.iso -volid cidata -joliet -rock user-data meta-data

FROM ${BASE}
RUN apt-get update && apt-get install -y --no-install-recommends qemu-system-x86 openssh-client && rm -rf /var/lib/apt/lists/*
COPY vm/vmboot vm/vmsh /usr/local/bin/
COPY --from=build --chown=65534:65534 /out /vm
