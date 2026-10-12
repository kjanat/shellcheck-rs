#!/bin/sh
set -eu
case "$KIND" in
	tarball)
		curl --silent --show-error --location --fail \
			--connect-timeout 20 --max-time 600 --retry 2 --retry-connrefused --retry-max-time 1800 \
			--output /tmp/src.tar "$SOURCE"
		echo "$SHA256  /tmp/src.tar" | sha256sum -c -
		tar -xf /tmp/src.tar --strip-components=1
		rm /tmp/src.tar
		;;
	git)
		git clone --quiet --depth 1 --branch "$TAG" "$SOURCE" .
		[ "$(git rev-parse HEAD)" = "$COMMIT" ]
		;;
	image)
		curl --silent --show-error --location --fail --output "image.${SOURCE##*.}" "$SOURCE"
		echo "$SHA256  image.${SOURCE##*.}" | sha256sum -c -
		;;
esac
