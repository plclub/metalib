coq_version = 8.9

# Retrieving the (short) hash of the current commit, as revision number
commit_hash := $(shell git rev-parse --short HEAD)

# Current Metalib version format is `<metalib commit hash>_coq<coq version>`
metalib_version = ${commit_hash}_coq${coq_version}

docker-image:
	@echo "Metalib: Building docker image for version ${metalib_version}"
	echo "ARG coq_version=${coq_version}" | cat - Dockerfile.static | sudo docker build -t metalib:latest -t metalib:${metalib_version} -
