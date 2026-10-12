#!/bin/sh
set -eu
case "$KIND" in
	tarball)
		curl --silent --show-error --location --fail --output /tmp/src.tar "$SOURCE"
		echo "$SHA256  /tmp/src.tar" | sha256sum -c -
		tar -xf /tmp/src.tar --strip-components=1
		rm /tmp/src.tar
		;;
	git)
		git clone --quiet --depth 1 --branch "$TAG" "$SOURCE" .
		[ "$(git rev-parse HEAD)" = "$COMMIT" ]
		;;
esac
