FROM gitpod/workspace-full-vnc

USER root

RUN apt-get -yq update \
	&& apt-get install -yq valgrind \
	&& apt-get install -y libsdl2-dev \
	&& apt-get install -y libuv1-dev \
	&& apt-get install -y check