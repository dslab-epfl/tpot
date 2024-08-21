/*SPECS*/ #include "spec_helpers.h" /*SYNTAX*/
/*SPECS*/ bool get_urb_status(struct urb *dev, enum urb_status *status) {
/*SPECS*/     struct usb_mouse *mouse = input_get_drvdata(dev);
/*SPECS*/     struct urb_hist_rec *rec = model__urb_get_record(mouse->irq);
/*SPECS*/     if (rec == NULL) 
/*SPECS*/         return false;

/*SPECS*/     *status = rec->status;
/*SPECS*/     return true;
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ bool dev_is_opened(struct input_dev *dev) {
/*SPECS*/     // the urb has been submitted.
/*SPECS*/     // it may be processed by the core and returned, or it may still be in the core's hands.
/*SPECS*/     enum urb_status s;
/*SPECS*/     return get_urb_status(dev, &s) && (s == SENT || s == RCV_BACK);
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ bool dev_is_closed(struct input_dev *dev) {
/*SPECS*/     enum urb_status s;
/*SPECS*/     return get_urb_status(dev, &s) && s == DONE;
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ bool dev_reportable(struct input_dev *dev) {
/*SPECS*/     return reportable_dev == dev;
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ bool dev_registered(struct input_dev *dev) {
/*SPECS*/     return registered_dev == dev;
/*SPECS*/ }  /*SYNTAX*/

/*SPECS*/ bool dev_initialized(struct device *d) {
/*SPECS*/     if (!names_obj(d->driver_data, struct usb_mouse))
/*SPECS*/         return false;
/*SPECS*/     struct usb_mouse *m = d->driver_data;
/*SPECS*/     return names_obj(m->irq, struct urb) &&
/*SPECS*/            names_obj(m->data, char[8]) &&
/*SPECS*/            names_obj(m->dev, struct input_dev) &&
/*SPECS*/            dev_registered(m->dev);
/*SPECS*/ }  /*SYNTAX*/