benchmark: docker_built
	docker run --rm -t -v $(shell pwd):/home/ecoop/local-scala-native local-scala-native bash -c "cd local-scala-native && ./run.sh"

interactive: docker_built
	docker run --rm -itv $(shell pwd):/home/ecoop/local-scala-native local-scala-native bash

docker_built:
	docker build -t local-scala-native .
	docker run --name lsn_post_build -t -v $(shell pwd):/home/ecoop/local-scala-native local-scala-native bash -c "cd local-scala-native && sbt sandbox/nativeLink"
	docker commit lsn_post_build local-scala-native
	docker container rm lsn_post_build
	touch docker_built

clean:
	find . -name target -type d -prune -exec rm -rf {} \;
	docker container rm lsn_post_build || true
	rm docker_built || true

image:
	$(MAKE) clean
	docker build -f ImageDockerfile -t local-scala-native .
