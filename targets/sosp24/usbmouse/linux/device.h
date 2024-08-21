#ifndef _LINUX_DEVICE_H
#define _LINUX_DEVICE_H

struct device {
  struct device	*parent;
  // TPot: The verifast case study simplified this struct. We put driver_data back in 
  // so that we can directly use the original linux functions in various models in linux_tpot.c.
  void	*driver_data;
};

int dev_err(const struct device *dev, const char *fmt, ...);
  //@ requires false;
  //@ ensures true;

#endif
