# test-plans impl Makefile (drop this directory into a fork of
# libp2p/test-plans as impl/leanp2p/<version>/, mirroring impl/go/<v>/).

image_name := leanp2p-v0.1

all: image.json

image.json:
	docker build -t $(image_name) -f Dockerfile ../..
	docker image inspect $(image_name) -f "{{.Id}}" | \
		xargs -I {} echo "{\"imageID\": \"{}\"}" > $@

.PHONY: clean all

clean:
	rm -f image.json
