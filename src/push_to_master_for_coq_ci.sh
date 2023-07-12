#!/bin/bash

git checkout master-for-coq-ci && \
git pull && \
git merge master && \
git push && \
echo "Successfully merged and pushed master into master-for-coq-ci"

git checkout master