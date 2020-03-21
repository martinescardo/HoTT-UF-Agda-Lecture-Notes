
## Installing Jekyll on Ubuntu 18.04

If you want to generate html pages from the notes and serve them up in your browser, you will need jekyll.

Here are steps you can follow on Ubuntu 18.04 to install the latest version.

```bash
sudo apt update
sudo apt -y upgrade
sudo reboot
sudo apt -y install make build-essential
sudo apt -y install ruby ruby-dev
export GEM_HOME=$HOME/gems
export PATH=$HOME/gems/bin:$PATH

source ~/.bashrc

gem install bundler
gem install jekyll
```

(Reference: https://computingforgeeks.com/how-to-install-jekyll-on-ubuntu-18-04/)

