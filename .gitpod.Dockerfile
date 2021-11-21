FROM gitpod/workspace-full-vnc

USER root

#.NET installed via .gitpod.yml task until the following issue is fixed: https://github.com/gitpod-io/gitpod/issues/5090
ENV DOTNET_VERSION=6.0
ENV DOTNET_ROOT=/workspace/.dotnet
ENV PATH=$PATH:$DOTNET_ROOT

RUN apt-get -yq update \
	&& apt-get install -yq valgrind \
	&& apt-get install -y libsdl2-dev \
	&& apt-get install -y libuv1-dev \
	&& apt-get install -y check