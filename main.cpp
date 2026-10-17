/*
    STOCKLINK v4 - quick-commerce store (console, single file, NO STL)

    C concepts used   : char arrays, pointers, structs, malloc/realloc/free,
                        FILE* I/O, printf/fgets, circular array queue,
                        array-based stack, linked list, Dijkstra on a matrix,
                        variadic functions (vsnprintf).
    C++ concepts used : classes, encapsulation, inheritance, abstract base
                        classes, virtual functions / polymorphism, constructors
                        and destructors (RAII), const-correctness, exceptions.

    Not used          : std::string, vector, map, unique_ptr, algorithm,
                        functional, iostream, iomanip, sstream, fstream.

    Logins:
      Customer : browse, search, delivery time, order, cancel order
      Manager  : inventory (expiry order), add/delete stock, reports, alerts,
                 all orders, cancelled orders, process/deliver, rush simulator
    Default manager login: admin / admin123

    Data files (new format, so old v3 files are simply ignored):
      users_v4.txt, inventory_v4.txt, orders_v4.txt,
      cancelled_orders_v4.txt, notifications_v4.txt
*/

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <cmath>
#include <ctime>
#include <cstdarg>

// ============================ CONSTANTS ============================
const int NAME_LEN        = 40;
const int EXTRA_LEN       = 24;
const int DATE_LEN        = 11;      // YYYY-MM-DD + '\0'
const int DOMAIN_LEN      = 16;
const int ROUTE_LEN       = 96;
const int LINE_LEN        = 512;
const int MAX_QUEUE       = 100;
const int MAX_NOTIF       = 100;
const int NOTIF_LEN       = 200;
const int MAX_CATALOG     = 256;
const int LOW_STOCK_LIMIT = 3;
const int EXPIRY_WARN_DAYS = 3;
const int PACKING_MINUTES = 5;
const int AREA_COUNT      = 5;
const double INF          = 1e9;
const double MIN_PER_KM   = 2.0;

const char *USERS_FILE         = "users_v4.txt";
const char *INVENTORY_FILE     = "inventory_v4.txt";
const char *ORDERS_FILE        = "orders_v4.txt";
const char *CANCELLED_FILE     = "cancelled_orders_v4.txt";
const char *NOTIFICATIONS_FILE = "notifications_v4.txt";

const char *DOMAINS[] = {"Food", "Electronics", "Clothing"};
const int DOMAIN_COUNT = 3;

enum OrderStatus { PENDING = 0, OUT_FOR_DELIVERY = 1, DELIVERED = 2, CANCELLED = 3 };
const char *STATUS_NAMES[] = {"PENDING", "OUT FOR DELIVERY", "DELIVERED", "CANCELLED"};

// ============================ STRING / INPUT HELPERS ============================
// [OWNER: Omkar]
struct InputClosed {};   // thrown when stdin reaches EOF

// [OWNER: SHARED (everyone)]
static void copyStr(char *dst, int cap, const char *src) {
    snprintf(dst, cap, "%s", src);
}

// [OWNER: Omkar]
static void trim(char *s) {
    int len = (int)strlen(s);
    while (len > 0 && isspace((unsigned char)s[len - 1])) s[--len] = '\0';
    int start = 0;
    while (s[start] && isspace((unsigned char)s[start])) ++start;
    if (start > 0) memmove(s, s + start, strlen(s + start) + 1);
}

// [OWNER: Nikhil]
static int cmpNoCase(const char *a, const char *b) {
    while (*a && *b) {
        int d = tolower((unsigned char)*a) - tolower((unsigned char)*b);
        if (d != 0) return d;
        ++a; ++b;
    }
    return tolower((unsigned char)*a) - tolower((unsigned char)*b);
}

// [OWNER: Nikhil]
static bool containsNoCase(const char *text, const char *query) {
    int n = (int)strlen(text), m = (int)strlen(query);
    if (m == 0) return true;
    for (int i = 0; i + m <= n; ++i) {
        int j = 0;
        while (j < m && tolower((unsigned char)text[i + j]) == tolower((unsigned char)query[j])) ++j;
        if (j == m) return true;
    }
    return false;
}

// '|' is our file delimiter, so it must never appear inside a field.
// [OWNER: Atyushman]
static void cleanField(char *s) {
    for (; *s; ++s) if (*s == '|') *s = '/';
}

// Splits `line` in place on '|'. Returns number of parts (max maxParts).
// [OWNER: Atyushman]
static int splitLine(char *line, char *parts[], int maxParts) {
    int n = 0;
    parts[n++] = line;
    for (char *p = line; *p && n < maxParts; ++p)
        if (*p == '|') { *p = '\0'; parts[n++] = p + 1; }
    return n;
}

// [OWNER: Atyushman]
static void stripNewline(char *s) {
    int len = (int)strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r')) s[--len] = '\0';
}

// [OWNER: Omkar]
static void readLine(char *out, int cap) {
    if (!fgets(out, cap, stdin)) throw InputClosed();
    if (!strchr(out, '\n')) {                       // line too long: discard the rest
        int c;
        while ((c = getchar()) != '\n' && c != EOF) {}
    }
    trim(out);
}

// [OWNER: Omkar]
static int readInt() {
    char buf[64];
    while (true) {
        readLine(buf, sizeof(buf));
        char *end;
        long v = strtol(buf, &end, 10);
        if (buf[0] != '\0' && *end == '\0') return (int)v;
        printf("Please enter a valid whole number: ");
    }
}

// [OWNER: Omkar]
static double readDouble() {
    char buf[64];
    while (true) {
        readLine(buf, sizeof(buf));
        char *end;
        double v = strtod(buf, &end);
        if (buf[0] != '\0' && *end == '\0' && v >= 0) return v;
        printf("Please enter a valid non-negative amount: ");
    }
}

// FNV-1a 64-bit. Demo-grade only. Real systems: bcrypt / argon2.
// [OWNER: Omkar]
static void hashPassword(const char *user, const char *pass, char *out, int cap) {
    unsigned long long h = 1469598103934665603ULL;
    const char *parts[3] = {user, ":", pass};
    for (int i = 0; i < 3; ++i)
        for (const char *p = parts[i]; *p; ++p) {
            h ^= (unsigned char)*p;
            h *= 1099511628211ULL;
        }
    snprintf(out, cap, "h:%016llx", h);
}

// ============================ DATE HELPERS ============================
// [OWNER: Nikhil]
static void datePlusDays(int days, char *out) {
    time_t now = time(NULL);
    struct tm t = *localtime(&now);
    t.tm_mday += days;
    mktime(&t);
    strftime(out, DATE_LEN, "%Y-%m-%d", &t);
}

// [OWNER: Nikhil]
static void nowString(char *out, int cap) {
    time_t now = time(NULL);
    strftime(out, cap, "%Y-%m-%d %H:%M", localtime(&now));
}

// [OWNER: Nikhil]
static bool isNoExpiry(const char *d) { return cmpNoCase(d, "NONE") == 0; }

// [OWNER: Nikhil]
static bool isLeap(int y) { return (y % 4 == 0 && y % 100 != 0) || y % 400 == 0; }

// [OWNER: Nikhil]
static bool isValidDate(const char *d) {
    if (strlen(d) != 10 || d[4] != '-' || d[7] != '-') return false;
    for (int i = 0; i < 10; ++i)
        if (i != 4 && i != 7 && !isdigit((unsigned char)d[i])) return false;
    int y, m, day;
    if (sscanf(d, "%d-%d-%d", &y, &m, &day) != 3) return false;
    if (m < 1 || m > 12 || day < 1) return false;
    static const int dim[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    return day <= dim[m - 1] + ((m == 2 && isLeap(y)) ? 1 : 0);
}

// [OWNER: Nikhil]
static bool isExpired(const char *d) {
    if (isNoExpiry(d)) return false;
    char today[DATE_LEN];
    datePlusDays(0, today);
    return strcmp(d, today) < 0;               // ISO dates compare correctly as text
}

// [OWNER: Nikhil]
static bool isExpirySoon(const char *d, int days) {
    if (isNoExpiry(d) || isExpired(d)) return false;
    char limit[DATE_LEN];
    datePlusDays(days, limit);
    return strcmp(d, limit) <= 0;
}

// Whole days from today until the date (negative = already expired).
// [OWNER: Nikhil]
static int daysUntil(const char *d) {
    if (!isValidDate(d)) return 0;
    int y, m, day;
    sscanf(d, "%d-%d-%d", &y, &m, &day);
    struct tm t = {};
    t.tm_year = y - 1900; t.tm_mon = m - 1; t.tm_mday = day; t.tm_hour = 12; t.tm_isdst = -1;
    time_t then = mktime(&t);

    time_t nowT = time(NULL);
    struct tm n = *localtime(&nowT);
    n.tm_hour = 12; n.tm_min = 0; n.tm_sec = 0; n.tm_isdst = -1;
    time_t today = mktime(&n);
    return (int)lround(difftime(then, today) / 86400.0);
}

// ============================ ITEM HIERARCHY (abstraction + inheritance) ============================
// [OWNER: Atyushman]
class Item {
private:
    int id;
    char name[NAME_LEN];
    int quantity;
    double price;
    char expiry[DATE_LEN];                 // YYYY-MM-DD or NONE
    char extra[EXTRA_LEN];                 // size / pack / warranty
    Item *next;
public:
    explicit Item(int itemId = 0) : id(itemId), quantity(0), price(0.0), next(NULL) {
        name[0] = '\0';
        copyStr(expiry, DATE_LEN, "NONE");
        copyStr(extra, EXTRA_LEN, "-");
    }
    virtual ~Item() {}

    int getId() const { return id; }
    const char *getName() const { return name; }
    int getQuantity() const { return quantity; }
    double getPrice() const { return price; }
    const char *getExpiry() const { return expiry; }
    const char *getExtra() const { return extra; }
    Item *getNext() const { return next; }

    void setName(const char *v) { copyStr(name, NAME_LEN, v); cleanField(name); }
    void setQuantity(int v) { quantity = v < 0 ? 0 : v; }
    void setPrice(double v) { price = v < 0 ? 0 : v; }
    void setExpiry(const char *v) { copyStr(expiry, DATE_LEN, isNoExpiry(v) ? "NONE" : v); }
    void setExtra(const char *v) {
        copyStr(extra, EXTRA_LEN, v); cleanField(extra);
        if (extra[0] == '\0') copyStr(extra, EXTRA_LEN, "-");
    }
    void setNext(Item *n) { next = n; }
    void reduce(int amount) { quantity = (quantity > amount) ? quantity - amount : 0; }

    bool expired() const { return isExpired(expiry); }
    bool expiringSoon() const { return isExpirySoon(expiry, EXPIRY_WARN_DAYS); }

    virtual const char *domain() const = 0;
    virtual bool needsExpiry() const = 0;
    virtual const char *extraLabel() const = 0;
};

// [OWNER: Atyushman]
class FoodItem : public Item {
public:
    explicit FoodItem(int id = 0) : Item(id) {}
    const char *domain() const override { return "Food"; }
    bool needsExpiry() const override { return true; }
    const char *extraLabel() const override { return "Pack"; }
};

// [OWNER: Atyushman]
class ElectronicItem : public Item {
public:
    explicit ElectronicItem(int id = 0) : Item(id) {}
    const char *domain() const override { return "Electronics"; }
    bool needsExpiry() const override { return false; }
    const char *extraLabel() const override { return "Warranty"; }
};

// [OWNER: Atyushman]
class ClothingItem : public Item {
public:
    explicit ClothingItem(int id = 0) : Item(id) {}
    const char *domain() const override { return "Clothing"; }
    bool needsExpiry() const override { return false; }
    const char *extraLabel() const override { return "Size"; }
};

// Factory: returns the right subclass for a category name.
// [OWNER: Atyushman]
static Item *makeItem(const char *domain, int id = 0) {
    if (strcmp(domain, "Food") == 0)        return new FoodItem(id);
    if (strcmp(domain, "Electronics") == 0) return new ElectronicItem(id);
    if (strcmp(domain, "Clothing") == 0)    return new ClothingItem(id);
    return NULL;
}

// [OWNER: Nikhil]
struct CatalogRow {
    char name[NAME_LEN];
    const char *domain;       // points at a string literal owned by the Item classes
    double price;
    int quantity;
};

// ============================ INVENTORY (sorted linked list) ============================
// [OWNER: Atyushman (class + list core); individual methods tagged below]
class Inventory {
private:
    Item *head;
    int nextId;

    // Earliest expiry first, items without expiry last, then A-Z.
    // [OWNER: Nikhil]
    static bool comesBefore(const Item *a, const Item *b) {
        bool aNone = isNoExpiry(a->getExpiry());
        bool bNone = isNoExpiry(b->getExpiry());
        if (aNone != bNone) return !aNone;
        if (!aNone) {
            int c = strcmp(a->getExpiry(), b->getExpiry());
            if (c != 0) return c < 0;
        }
        return cmpNoCase(a->getName(), b->getName()) < 0;
    }

    // [OWNER: Atyushman]
    static bool sameProduct(const Item *a, const char *name, const char *domain) {
        return strcmp(a->domain(), domain) == 0 && cmpNoCase(a->getName(), name) == 0;
    }

    // [OWNER: Nikhil]
    void insertSorted(Item *node) {
        if (!head || comesBefore(node, head)) {
            node->setNext(head);
            head = node;
            return;
        }
        Item *cur = head;
        while (cur->getNext() && !comesBefore(node, cur->getNext())) cur = cur->getNext();
        node->setNext(cur->getNext());
        cur->setNext(node);
    }

public:
    // [OWNER: Atyushman]
    Inventory() : head(NULL), nextId(1) {}
    ~Inventory() {
        while (head) {
            Item *n = head->getNext();
            delete head;
            head = n;
        }
    }
    Inventory(const Inventory &) = delete;
    Inventory &operator=(const Inventory &) = delete;

    // [OWNER: Atyushman]
    int allocateId() { return nextId++; }

    // Adds a batch; keeps name spelling and price identical across batches of one product.
    // [OWNER: Atyushman]
    void add(Item *node) {
        for (Item *p = head; p; p = p->getNext())
            if (sameProduct(p, node->getName(), node->domain())) { node->setName(p->getName()); break; }
        insertSorted(node);
        for (Item *p = head; p; p = p->getNext())
            if (sameProduct(p, node->getName(), node->domain())) p->setPrice(node->getPrice());
        if (node->getId() >= nextId) nextId = node->getId() + 1;
    }

    // [OWNER: Atyushman]
    bool load() {
        FILE *in = fopen(INVENTORY_FILE, "r");
        if (!in) return false;
        char line[LINE_LEN];
        int count = 0;
        while (fgets(line, sizeof(line), in)) {
            stripNewline(line);
            char *p[7];
            if (splitLine(line, p, 7) < 7) continue;
            Item *item = makeItem(p[1], atoi(p[0]));
            if (!item) continue;
            item->setName(p[2]);
            item->setQuantity(atoi(p[3]));
            item->setPrice(atof(p[4]));
            item->setExpiry(p[5]);
            item->setExtra(p[6]);
            add(item);
            ++count;
        }
        fclose(in);
        return count > 0;
    }

    // [OWNER: Atyushman]
    void save() const {
        FILE *out = fopen(INVENTORY_FILE, "w");
        if (!out) return;
        for (const Item *p = head; p; p = p->getNext())
            fprintf(out, "%d|%s|%s|%d|%.2f|%s|%s\n", p->getId(), p->domain(), p->getName(),
                    p->getQuantity(), p->getPrice(), p->getExpiry(), p->getExtra());
        fclose(out);
    }

    // [OWNER: Atyushman]
    void seedDefaults() {
        struct Seed { const char *domain, *name; int qty; double price; int days; const char *extra; };
        static const Seed seeds[] = {
            {"Food", "Biscuit Pack",        40,  10.0, 120, "1 pack"},
            {"Food", "Chocolate Cookies",   30,  30.0, 150, "1 pack"},
            {"Food", "Potato Chips",        35,  20.0,  90, "1 pack"},
            {"Food", "Instant Noodles",     40,  14.0, 180, "1 pack"},
            {"Food", "Sunflower Oil 1L",    20, 165.0, 240, "1 L"},
            {"Food", "Mustard Oil 1L",      18, 175.0, 240, "1 L"},
            {"Food", "Fruit Juice 1L",      25,  99.0,  60, "1 L"},
            {"Food", "Orange Juice 200ml",  30,  25.0,  45, "200 ml"},
            {"Food", "Cold Drink 750ml",    30,  40.0,  80, "750 ml"},
            {"Food", "Salt 1kg",            30,  20.0, 365, "1 kg"},
            {"Food", "Sugar 1kg",           25,  45.0, 300, "1 kg"},
            {"Food", "Atta 5kg",            12, 260.0, 150, "5 kg"},
            {"Food", "Basmati Rice 5kg",    14, 540.0, 300, "5 kg"},
            {"Food", "Toor Dal 1kg",        16, 150.0, 270, "1 kg"},
            {"Food", "Tea Powder 250g",     18, 110.0, 200, "250 g"},
            {"Food", "Milk 500ml",          12,  28.0,   2, "500 ml"},   // older batch, sold first (FEFO)
            {"Food", "Milk 500ml",          20,  28.0,   6, "500 ml"},   // newer batch
            {"Food", "Curd 400g",           15,  35.0,   7, "400 g"},
            {"Food", "Butter 100g",         10,  56.0,  45, "100 g"},
            {"Food", "Bread",               20,  40.0,   4, "1 loaf"},
            {"Food", "Fruit Jam 500g",      12, 120.0, 200, "500 g"},
            {"Electronics", "iPhone 15",          5, 69900.0, -1, "12 months"},
            {"Electronics", "Laptop",             6, 54999.0, -1, "24 months"},
            {"Electronics", "Earphones",         20,   499.0, -1, "6 months"},
            {"Electronics", "Phone Charger",     25,   399.0, -1, "12 months"},
            {"Electronics", "USB Cable",         30,   149.0, -1, "6 months"},
            {"Electronics", "Power Bank",        10,  1199.0, -1, "12 months"},
            {"Electronics", "Bluetooth Speaker",  6,  1599.0, -1, "12 months"},
            {"Electronics", "Smart Watch",        8,  2999.0, -1, "12 months"},
            {"Clothing", "T-Shirt",   25,  299.0, -1, "M"},
            {"Clothing", "Jeans",     15,  899.0, -1, "32"},
            {"Clothing", "Socks",     40,   99.0, -1, "Free size"},
            {"Clothing", "Jacket",     8, 1499.0, -1, "L"}
        };
        for (const Seed &s : seeds) {
            Item *item = makeItem(s.domain, allocateId());
            item->setName(s.name);
            item->setQuantity(s.qty);
            item->setPrice(s.price);
            char date[DATE_LEN];
            if (s.days < 0) copyStr(date, DATE_LEN, "NONE"); else datePlusDays(s.days, date);
            item->setExpiry(date);
            item->setExtra(s.extra);
            add(item);
        }
        save();
    }

    // Customer view: batches merged per product, expired hidden, sorted A-Z.
    // Fills rows[] and returns how many rows were written.
    // [OWNER: Nikhil]
    int catalog(const char *domainFilter, CatalogRow rows[], int maxRows) const {
        int n = 0;
        for (const Item *p = head; p; p = p->getNext()) {
            if (p->expired()) continue;
            if (domainFilter[0] && strcmp(p->domain(), domainFilter) != 0) continue;
            int k = 0;
            while (k < n && !(strcmp(rows[k].domain, p->domain()) == 0 &&
                              cmpNoCase(rows[k].name, p->getName()) == 0)) ++k;
            if (k < n) { rows[k].quantity += p->getQuantity(); continue; }
            if (n == maxRows) continue;
            copyStr(rows[n].name, NAME_LEN, p->getName());
            rows[n].domain = p->domain();
            rows[n].price = p->getPrice();
            rows[n].quantity = p->getQuantity();
            ++n;
        }
        for (int i = 1; i < n; ++i) {                 // insertion sort A-Z
            CatalogRow key = rows[i];
            int j = i - 1;
            while (j >= 0 && cmpNoCase(rows[j].name, key.name) > 0) { rows[j + 1] = rows[j]; --j; }
            rows[j + 1] = key;
        }
        return n;
    }

    // [OWNER: Rahil]
    int available(const char *name, const char *domain) const {
        int total = 0;
        for (const Item *p = head; p; p = p->getNext())
            if (!p->expired() && sameProduct(p, name, domain)) total += p->getQuantity();
        return total;
    }

    // FEFO: take stock from the batch that expires first.
    // [OWNER: Rahil]
    bool consume(const char *name, const char *domain, int qty) {
        if (qty <= 0 || available(name, domain) < qty) return false;
        int need = qty;
        for (Item *p = head; p && need > 0; p = p->getNext()) {
            if (p->expired() || !sameProduct(p, name, domain)) continue;
            int take = need < p->getQuantity() ? need : p->getQuantity();
            p->reduce(take);
            need -= take;
        }
        save();
        return true;
    }

    // Cancelled order: stock goes back into the earliest valid batch.
    // [OWNER: Rahil]
    bool restock(const char *name, const char *domain, int qty) {
        for (Item *p = head; p; p = p->getNext()) {
            if (p->expired() || !sameProduct(p, name, domain)) continue;
            p->setQuantity(p->getQuantity() + qty);
            save();
            return true;
        }
        return false;
    }

    // [OWNER: Atyushman]
    bool removeById(int id) {
        Item *prev = NULL, *cur = head;
        while (cur) {
            if (cur->getId() == id) {
                if (prev) prev->setNext(cur->getNext()); else head = cur->getNext();
                delete cur;
                save();
                return true;
            }
            prev = cur;
            cur = cur->getNext();
        }
        return false;
    }

    // [OWNER: Aman]
    int removeExpired() {
        int removed = 0;
        Item *prev = NULL, *cur = head;
        while (cur) {
            Item *next = cur->getNext();
            if (cur->expired()) {
                if (prev) prev->setNext(next); else head = next;
                delete cur;
                ++removed;
            } else prev = cur;
            cur = next;
        }
        if (removed) save();
        return removed;
    }

    // [OWNER: Aman]
    int countExpired() const {
        int n = 0;
        for (const Item *p = head; p; p = p->getNext()) if (p->expired() && p->getQuantity() > 0) ++n;
        return n;
    }

    // [OWNER: Aman]
    int countExpiringSoon() const {
        int n = 0;
        for (const Item *p = head; p; p = p->getNext()) if (p->expiringSoon() && p->getQuantity() > 0) ++n;
        return n;
    }

    // [OWNER: Nikhil]
    void showInternal() const {
        printf("\n------------------ INVENTORY (earliest expiry first) ------------------\n");
        printf("%-5s%-13s%-22s%-6s%-13s%-12s%s\n", "ID", "Category", "Product", "Qty", "Price", "Expiry", "Status | Details");
        printf("%s\n", "-----------------------------------------------------------------------------------------------");
        if (!head) printf("Inventory is empty.\n");
        for (const Item *p = head; p; p = p->getNext()) {
            const char *status = p->expired() ? "EXPIRED" : p->expiringSoon() ? "EXPIRING SOON"
                               : p->getQuantity() == 0 ? "EMPTY" : "OK";
            char price[24];
            snprintf(price, sizeof(price), "Rs %.2f", p->getPrice());
            printf("%-5d%-13s%-22.20s%-6d%-13s%-12s%s | %s: %s\n", p->getId(), p->domain(), p->getName(),
                   p->getQuantity(), price, p->getExpiry(), status, p->extraLabel(), p->getExtra());
        }
    }

    // [OWNER: Nikhil]
    bool printExpiryReport(int days) const {
        bool any = false;
        printf("%-5s%-22s%-6s%-12s%s\n", "ID", "Product", "Qty", "Expiry", "Status");
        printf("------------------------------------------------------------\n");
        for (const Item *p = head; p; p = p->getNext()) {
            if (p->getQuantity() == 0 || isNoExpiry(p->getExpiry())) continue;
            int daysLeft = daysUntil(p->getExpiry());
            if (daysLeft > days) continue;
            char status[40];
            if (daysLeft < 0) snprintf(status, sizeof(status), "EXPIRED %d day(s) ago", -daysLeft);
            else if (daysLeft == 0) copyStr(status, sizeof(status), "EXPIRES TODAY");
            else snprintf(status, sizeof(status), "%d day(s) left", daysLeft);
            printf("%-5d%-22.20s%-6d%-12s%s\n", p->getId(), p->getName(), p->getQuantity(), p->getExpiry(), status);
            any = true;
        }
        return any;
    }
};

// ============================ ORDERS ============================
// [OWNER: Rahil]
struct Order {
    int id;
    int customerId;
    char customerName[NAME_LEN];
    char productName[NAME_LEN];
    char domain[DOMAIN_LEN];
    int quantity;
    double total;
    int status;                 // OrderStatus
    int area;
    int etaMinutes;
    char traffic[16];
    char route[ROUTE_LEN];
    double km;
};

// Circular-array FIFO queue. It stores order IDs only, not whole orders.
// [OWNER: Aman]
class OrderQueue {
private:
    int data[MAX_QUEUE];
    int frontIndex, rearIndex, count;
public:
    OrderQueue() : frontIndex(0), rearIndex(0), count(0) {}
    bool enqueue(int orderId) {
        if (count == MAX_QUEUE) return false;
        data[rearIndex] = orderId;
        rearIndex = (rearIndex + 1) % MAX_QUEUE;
        ++count;
        return true;
    }
    bool dequeue(int &orderId) {
        if (count == 0) return false;
        orderId = data[frontIndex];
        frontIndex = (frontIndex + 1) % MAX_QUEUE;
        --count;
        return true;
    }
    bool full() const { return count == MAX_QUEUE; }
};

// ============================ MANAGER ALERT STACK (array-based LIFO) ============================
// [OWNER: Aman]
class NotificationStack {
private:
    char text[MAX_NOTIF][NOTIF_LEN];
    bool seen[MAX_NOTIF];
    int topIndex;
public:
    NotificationStack() : topIndex(-1) {}

    void push(const char *message, bool isSeen = false) {
        if (topIndex == MAX_NOTIF - 1) {              // full: drop the oldest
            memmove(text[0], text[1], (size_t)topIndex * NOTIF_LEN);
            memmove(seen, seen + 1, (size_t)topIndex * sizeof(bool));
            --topIndex;
        }
        ++topIndex;
        copyStr(text[topIndex], NOTIF_LEN, message);
        cleanField(text[topIndex]);
        seen[topIndex] = isSeen;
    }

    bool pop(char *out, int cap) {
        if (topIndex < 0) return false;
        copyStr(out, cap, text[topIndex--]);
        return true;
    }

    bool empty() const { return topIndex < 0; }
    void clear() { topIndex = -1; }

    int unseenCount() const {
        int n = 0;
        for (int i = 0; i <= topIndex; ++i) if (!seen[i]) ++n;
        return n;
    }

    void markAllSeen() { for (int i = 0; i <= topIndex; ++i) seen[i] = true; }

    void showNewestFirst() const {
        if (empty()) { printf("No alerts. Everything is calm.\n"); return; }
        printf("\n--- ALERTS INBOX (newest first) ---\n");
        for (int i = topIndex; i >= 0; --i)
            printf("%d. %s%s\n", topIndex - i + 1, seen[i] ? "" : "[NEW] ", text[i]);
    }

    void showPopup() {
        int unseen = unseenCount();
        if (unseen == 0) return;
        printf("\n+==================================================+\n");
        printf("  (!) %d NEW ALERT(S) FOR THE MANAGER\n", unseen);
        printf("+==================================================+\n");
        int shown = 0;
        for (int i = topIndex; i >= 0 && shown < 5; --i) {
            if (seen[i]) continue;
            printf("  * %s\n", text[i]);
            seen[i] = true;
            ++shown;
        }
        if (unseen > shown) printf("  ... and %d more (see Alerts inbox)\n", unseen - shown);
        printf("+==================================================+\n");
    }

    void loadFromFile() {
        FILE *in = fopen(NOTIFICATIONS_FILE, "r");
        if (!in) return;
        char line[NOTIF_LEN + 8];
        while (fgets(line, sizeof(line), in)) {       // push() already drops the oldest when full
            stripNewline(line);
            if (strlen(line) > 2) push(line + 2, line[0] == '1');
        }
        fclose(in);
    }

    void saveToFile() const {
        FILE *out = fopen(NOTIFICATIONS_FILE, "w");
        if (!out) return;
        for (int i = 0; i <= topIndex; ++i) fprintf(out, "%c|%s\n", seen[i] ? '1' : '0', text[i]);
        fclose(out);
    }
};

// ============================ DELIVERY MAP (graph + Dijkstra + random traffic) ============================
// [OWNER: Rahil]
struct RouteQuote {
    double km;
    double travelMinutes;
    char path[ROUTE_LEN];
    const char *traffic;
};

// [OWNER: Rahil]
class DeliveryMap {
private:
    double km[AREA_COUNT][AREA_COUNT];
    double factor[AREA_COUNT][AREA_COUNT];
public:
    DeliveryMap() {
        // 0=Central (the store), 1=North, 2=East, 3=South, 4=West
        const double base[AREA_COUNT][AREA_COUNT] = {
            {0, 2.0, 4.0, 7.0, 3.0},
            {2.0, 0, 1.5, INF, 4.0},
            {4.0, 1.5, 0, 2.0, 5.0},
            {7.0, INF, 2.0, 0, 2.0},
            {3.0, 4.0, 5.0, 2.0, 0}
        };
        memcpy(km, base, sizeof(km));
        refreshTraffic();
    }

    static const char *areaName(int a) {
        static const char *names[] = {"Central", "North", "East", "South", "West"};
        return (a < 0 || a >= AREA_COUNT) ? names[0] : names[a];
    }

    static const char *levelName(double f) {
        if (f < 1.15) return "Light";
        if (f < 1.7)  return "Moderate";
        if (f < 2.4)  return "Heavy";
        return "Severe jam";
    }

    void refreshTraffic() {
        for (int i = 0; i < AREA_COUNT; ++i) {
            factor[i][i] = 1.0;
            for (int j = i + 1; j < AREA_COUNT; ++j) {
                int r = rand() % 100;
                factor[i][j] = factor[j][i] = (r < 40) ? 1.0 : (r < 70) ? 1.5 : (r < 90) ? 2.2 : 3.0;
            }
        }
    }

    // Dijkstra from the store (node 0); edge cost = minutes including traffic.
    RouteQuote quote(int destination) const {
        if (destination < 0 || destination >= AREA_COUNT) destination = 0;
        double dist[AREA_COUNT];
        int prev[AREA_COUNT];
        bool visited[AREA_COUNT];
        for (int i = 0; i < AREA_COUNT; ++i) { dist[i] = INF; prev[i] = -1; visited[i] = false; }
        dist[0] = 0;

        for (int step = 0; step < AREA_COUNT; ++step) {
            int u = -1;
            for (int i = 0; i < AREA_COUNT; ++i)
                if (!visited[i] && (u == -1 || dist[i] < dist[u])) u = i;
            if (u == -1 || dist[u] >= INF) break;
            visited[u] = true;
            for (int v = 0; v < AREA_COUNT; ++v) {
                if (v == u || km[u][v] >= INF) continue;
                double minutes = km[u][v] * MIN_PER_KM * factor[u][v];
                if (dist[u] + minutes < dist[v]) { dist[v] = dist[u] + minutes; prev[v] = u; }
            }
        }

        int nodes[AREA_COUNT], len = 0;
        for (int at = destination; at != -1 && len < AREA_COUNT; at = prev[at]) nodes[len++] = at;

        RouteQuote q;
        q.km = 0;
        q.path[0] = '\0';
        for (int i = len - 1; i >= 0; --i) {          // nodes[] is destination -> store, so walk backwards
            if (i < len - 1) {
                strncat(q.path, " -> ", ROUTE_LEN - strlen(q.path) - 1);
                q.km += km[nodes[i + 1]][nodes[i]];
            }
            strncat(q.path, areaName(nodes[i]), ROUTE_LEN - strlen(q.path) - 1);
        }
        q.travelMinutes = dist[destination];
        double ratio = q.km > 0 ? q.travelMinutes / (q.km * MIN_PER_KM) : 1.0;
        q.traffic = levelName(ratio);
        return q;
    }

    // [OWNER: Rahil]
    void showReport() const {
        printf("\n--- LIVE ROAD TRAFFIC (randomly generated) ---\n");
        for (int i = 0; i < AREA_COUNT; ++i)
            for (int j = i + 1; j < AREA_COUNT; ++j)
                if (km[i][j] < INF)
                    printf("%-8s <-> %-8s %.1f km | %s (x%.1f)\n", areaName(i), areaName(j),
                           km[i][j], levelName(factor[i][j]), factor[i][j]);
        printf("\nDelivery time from the store (includes %d min packing):\n", PACKING_MINUTES);
        for (int d = 0; d < AREA_COUNT; ++d) {
            RouteQuote q = quote(d);
            printf("  %-8s: about %d min | traffic: %s | route: %s\n", areaName(d),
                   PACKING_MINUTES + (int)(q.travelMinutes + 0.5), q.traffic, q.path);
        }
    }
};

// ============================ USERS (abstract base + 2 subclasses) ============================
// [OWNER: Omkar]
struct UserRecord {
    int id;
    char name[NAME_LEN];
    char username[32];
    char password[32];          // "h:<16 hex digits>"
    char role[12];              // CUSTOMER or MANAGER
};

// [OWNER: Omkar]
class User {
protected:
    int id;
    char name[NAME_LEN];
public:
    explicit User(const UserRecord &u) : id(u.id) { copyStr(name, NAME_LEN, u.name); }
    virtual ~User() {}
    int getId() const { return id; }
    const char *getName() const { return name; }
    virtual void showDashboard() const = 0;
};

// [OWNER: Omkar]
class Customer : public User {
public:
    explicit Customer(const UserRecord &u) : User(u) {}
    void showDashboard() const override { printf("\n========== CUSTOMER DASHBOARD ==========\nWelcome, %s!\n", name); }
};

// [OWNER: Omkar]
class Manager : public User {
public:
    explicit Manager(const UserRecord &u) : User(u) {}
    void showDashboard() const override { printf("\n========== MANAGER DASHBOARD ==========\nWelcome, %s!\n", name); }
};

// ============================ MAIN APPLICATION ============================
// [OWNER: SHARED shell; methods tagged below]
class StockLink {
private:
    Inventory inventory;
    OrderQueue orderQueue;
    NotificationStack notifications;
    DeliveryMap roads;

    Order *orders;          // growable array (malloc / realloc / free)
    int orderCount, orderCap;
    UserRecord *users;
    int userCount, userCap;
    int nextOrderId, nextUserId, guestCounter;

    // printf-style alert: notify("ORDER #%d ...", id);
    // [OWNER: Aman]
    void notify(const char *fmt, ...) {
        char msg[NOTIF_LEN];
        va_list args;
        va_start(args, fmt);
        vsnprintf(msg, sizeof(msg), fmt, args);
        va_end(args);
        notifications.push(msg);
        notifications.saveToFile();
    }

    // ---------- dynamic arrays ----------
    // [OWNER: Rahil]
    bool addOrder(const Order &o) {
        if (orderCount == orderCap) {
            int cap = orderCap ? orderCap * 2 : 32;
            Order *bigger = (Order *)realloc(orders, (size_t)cap * sizeof(Order));
            if (!bigger) return false;
            orders = bigger;
            orderCap = cap;
        }
        orders[orderCount++] = o;
        return true;
    }

    // [OWNER: Omkar]
    bool addUser(const UserRecord &u) {
        if (userCount == userCap) {
            int cap = userCap ? userCap * 2 : 16;
            UserRecord *bigger = (UserRecord *)realloc(users, (size_t)cap * sizeof(UserRecord));
            if (!bigger) return false;
            users = bigger;
            userCap = cap;
        }
        users[userCount++] = u;
        return true;
    }

    // [OWNER: SHARED (Rahil + Aman)]
    Order *findOrder(int id) {
        for (int i = 0; i < orderCount; ++i) if (orders[i].id == id) return &orders[i];
        return NULL;
    }

    // ---------- users ----------
    // [OWNER: Omkar]
    void loadUsers() {
        FILE *in = fopen(USERS_FILE, "r");
        char line[LINE_LEN];
        while (in && fgets(line, sizeof(line), in)) {
            stripNewline(line);
            char *p[5];
            if (splitLine(line, p, 5) < 5) continue;
            UserRecord u;
            u.id = atoi(p[0]);
            copyStr(u.name, sizeof(u.name), p[1]);
            copyStr(u.username, sizeof(u.username), p[2]);
            copyStr(u.password, sizeof(u.password), p[3]);
            copyStr(u.role, sizeof(u.role), p[4]);
            addUser(u);
        }
        if (in) fclose(in);
        if (userCount == 0) {
            UserRecord a;
            a.id = 1;
            copyStr(a.name, sizeof(a.name), "StockLink Manager");
            copyStr(a.username, sizeof(a.username), "admin");
            hashPassword("admin", "admin123", a.password, sizeof(a.password));
            copyStr(a.role, sizeof(a.role), "MANAGER");
            addUser(a);
            saveUsers();
        }
        nextUserId = 1;
        for (int i = 0; i < userCount; ++i) if (users[i].id >= nextUserId) nextUserId = users[i].id + 1;
    }

    // [OWNER: Omkar]
    void saveUsers() const {
        FILE *out = fopen(USERS_FILE, "w");
        if (!out) return;
        for (int i = 0; i < userCount; ++i)
            fprintf(out, "%d|%s|%s|%s|%s\n", users[i].id, users[i].name, users[i].username,
                    users[i].password, users[i].role);
        fclose(out);
    }

    // [OWNER: Omkar]
    bool usernameExists(const char *username) const {
        for (int i = 0; i < userCount; ++i) if (strcmp(users[i].username, username) == 0) return true;
        return false;
    }

    // [OWNER: Omkar]
    UserRecord *authenticate(const char *username, const char *password) {
        char h[32];
        hashPassword(username, password, h, sizeof(h));
        for (int i = 0; i < userCount; ++i)
            if (strcmp(users[i].username, username) == 0 && strcmp(users[i].password, h) == 0)
                return &users[i];
        return NULL;
    }

    // [OWNER: Omkar]
    void registerUser(const char *role) {
        bool mgr = strcmp(role, "MANAGER") == 0;
        printf(mgr ? "\n--- CREATE STAFF (MANAGER) ACCOUNT ---\n" : "\n--- CREATE CUSTOMER ACCOUNT ---\n");
        UserRecord u;
        char password[32];
        printf("Full name: ");       readLine(u.name, sizeof(u.name));
        printf("Choose username: "); readLine(u.username, sizeof(u.username));
        cleanField(u.name);
        cleanField(u.username);
        if (!u.name[0] || !u.username[0]) { printf("Name and username cannot be empty.\n"); return; }
        if (usernameExists(u.username)) { printf("That username already exists.\n"); return; }
        printf("Choose password: ");  readLine(password, sizeof(password));
        if (!password[0]) { printf("Password cannot be empty.\n"); return; }

        u.id = nextUserId++;
        hashPassword(u.username, password, u.password, sizeof(u.password));
        copyStr(u.role, sizeof(u.role), role);
        if (!addUser(u)) { printf("Out of memory.\n"); return; }
        saveUsers();
        printf("Account created successfully.\n");
        if (!mgr) notify("NEW CUSTOMER registered: %s (%s)", u.name, u.username);
    }

    // ---------- order files ----------
    // [OWNER: Rahil]
    void loadOrders() {
        FILE *in = fopen(ORDERS_FILE, "r");
        if (!in) return;
        char line[LINE_LEN * 2];
        while (fgets(line, sizeof(line), in)) {
            stripNewline(line);
            char *p[13];
            if (splitLine(line, p, 13) < 13) continue;
            Order o;
            o.id = atoi(p[0]);
            o.customerId = atoi(p[1]);
            copyStr(o.customerName, NAME_LEN, p[2]);
            copyStr(o.productName, NAME_LEN, p[3]);
            copyStr(o.domain, DOMAIN_LEN, p[4]);
            o.quantity = atoi(p[5]);
            o.total = atof(p[6]);
            o.status = atoi(p[7]);
            o.area = atoi(p[8]);
            o.etaMinutes = atoi(p[9]);
            copyStr(o.traffic, sizeof(o.traffic), p[10]);
            copyStr(o.route, ROUTE_LEN, p[11]);
            o.km = atof(p[12]);
            if (o.status < PENDING || o.status > CANCELLED) continue;
            if (addOrder(o) && o.id >= nextOrderId) nextOrderId = o.id + 1;
        }
        fclose(in);
    }

    // [OWNER: Rahil]
    void saveOrders() const {
        FILE *out = fopen(ORDERS_FILE, "w");
        if (!out) return;
        for (int i = 0; i < orderCount; ++i) {
            const Order &o = orders[i];
            fprintf(out, "%d|%d|%s|%s|%s|%d|%.2f|%d|%d|%d|%s|%s|%.1f\n", o.id, o.customerId,
                    o.customerName, o.productName, o.domain, o.quantity, o.total, o.status,
                    o.area, o.etaMinutes, o.traffic, o.route, o.km);
        }
        fclose(out);
    }

    // Cancelled orders go to their own file (manager only).
    // [OWNER: Aman]
    void logCancellation(const Order &o) const {
        FILE *out = fopen(CANCELLED_FILE, "a");
        if (!out) return;
        char when[24];
        nowString(when, sizeof(when));
        fprintf(out, "%d|%d|%s|%s|%s|%d|%.2f|%s|%s\n", o.id, o.customerId, o.customerName,
                o.productName, o.domain, o.quantity, o.total, DeliveryMap::areaName(o.area), when);
        fclose(out);
    }

    // ---------- shared order logic (customers AND the rush simulator) ----------
    // Returns NULL on success, otherwise an error message.
    // [OWNER: Rahil]
    const char *createOrder(int customerId, const char *customerName, const CatalogRow &row,
                            int qty, int area, Order &out) {
        if (qty <= 0 || qty > inventory.available(row.name, row.domain))
            return "Invalid quantity or not enough stock.";
        if (orderQueue.full()) return "Order queue is full. Please try again later.";

        roads.refreshTraffic();
        RouteQuote quote = roads.quote(area);
        if (!inventory.consume(row.name, row.domain, qty)) return "Stock changed, please try again.";

        out.id = nextOrderId++;
        out.customerId = customerId;
        copyStr(out.customerName, NAME_LEN, customerName);
        copyStr(out.productName, NAME_LEN, row.name);
        copyStr(out.domain, DOMAIN_LEN, row.domain);
        out.quantity = qty;
        out.total = qty * row.price;
        out.status = PENDING;
        out.area = area;
        out.etaMinutes = PACKING_MINUTES + (int)(quote.travelMinutes + 0.5);
        copyStr(out.traffic, sizeof(out.traffic), quote.traffic);
        copyStr(out.route, ROUTE_LEN, quote.path);
        out.km = quote.km;

        if (!addOrder(out)) return "Out of memory.";
        orderQueue.enqueue(out.id);
        saveOrders();

        notify("NEW ORDER #%d from %s: %d x %s -> %s, delivery ~%d min (traffic: %s)", out.id,
               customerName, qty, row.name, DeliveryMap::areaName(area), out.etaMinutes, quote.traffic);

        int left = inventory.available(row.name, row.domain);
        if (left == 0) notify("OUT OF STOCK: %s is finished - please restock!", row.name);
        else if (left <= LOW_STOCK_LIMIT) notify("LOW STOCK: %s has only %d left - restock soon!", row.name, left);
        return NULL;
    }

    // ---------- customer screens ----------
    // [OWNER: Atyushman]
    static void printDomainChoices() {
        for (int i = 0; i < DOMAIN_COUNT; ++i) printf("  %d. %s", i + 1, DOMAINS[i]);
    }

    // [OWNER: Nikhil]
    static const char *askDomainFilter() {
        printf("Category: 0. All");
        printDomainChoices();
        printf("\nChoose: ");
        int c = readInt();
        return (c >= 1 && c <= DOMAIN_COUNT) ? DOMAINS[c - 1] : "";
    }

    // [OWNER: Nikhil]
    static void printCatalog(const CatalogRow rows[], int n) {
        printf("\n---------------- STORE (A - Z) ----------------\n");
        printf("%-5s%-24s%-14s%-14s%s\n", "No", "Product", "Category", "Price", "Availability");
        printf("--------------------------------------------------------------------\n");
        if (n == 0) printf("No products to display.\n");
        for (int i = 0; i < n; ++i) {
            char price[24], avail[24];
            snprintf(price, sizeof(price), "Rs %.2f", rows[i].price);
            if (rows[i].quantity == 0) copyStr(avail, sizeof(avail), "Out of stock");
            else if (rows[i].quantity <= LOW_STOCK_LIMIT) snprintf(avail, sizeof(avail), "Only %d left", rows[i].quantity);
            else copyStr(avail, sizeof(avail), "In stock");
            printf("%-5d%-24.22s%-14s%-14s%s\n", i + 1, rows[i].name, rows[i].domain, price, avail);
        }
    }

    // [OWNER: Rahil]
    static int askArea() {
        printf("\nDelivery area: 0. Central  1. North  2. East  3. South  4. West\nYour area number: ");
        int a = readInt();
        if (a < 0 || a >= AREA_COUNT) { printf("Invalid area.\n"); return -1; }
        return a;
    }

    // [OWNER: Nikhil]
    void browseProducts() {
        CatalogRow rows[MAX_CATALOG];
        int n = inventory.catalog(askDomainFilter(), rows, MAX_CATALOG);
        printCatalog(rows, n);
    }

    // [OWNER: Nikhil]
    void searchProducts() {
        char query[NAME_LEN];
        printf("Enter product name to search: ");
        readLine(query, sizeof(query));
        CatalogRow all[MAX_CATALOG], hits[MAX_CATALOG];
        int n = inventory.catalog("", all, MAX_CATALOG), h = 0;
        for (int i = 0; i < n; ++i) if (containsNoCase(all[i].name, query)) hits[h++] = all[i];
        printCatalog(hits, h);
    }

    // [OWNER: Rahil]
    void checkDeliveryTime() {
        int area = askArea();
        if (area < 0) return;
        roads.refreshTraffic();
        RouteQuote q = roads.quote(area);
        printf("\n--- DELIVERY ESTIMATE ---\n"
               "To              : %s\n"
               "Distance        : %.1f km\n"
               "Route           : %s\n"
               "Traffic now     : %s\n"
               "Delivery time   : about %d minutes (includes %d min packing)\n",
               DeliveryMap::areaName(area), q.km, q.path, q.traffic,
               PACKING_MINUTES + (int)(q.travelMinutes + 0.5), PACKING_MINUTES);
    }

    // [OWNER: Rahil]
    void placeOrder(const User &user) {
        CatalogRow rows[MAX_CATALOG];
        int n = inventory.catalog(askDomainFilter(), rows, MAX_CATALOG);
        if (n == 0) { printf("No products available.\n"); return; }
        printCatalog(rows, n);

        printf("\nEnter product number (0 to cancel): ");
        int number = readInt();
        if (number == 0) return;
        if (number < 1 || number > n) { printf("Invalid number.\n"); return; }
        const CatalogRow &row = rows[number - 1];
        if (row.quantity == 0) { printf("%s is out of stock.\n", row.name); return; }

        printf("Quantity to order: ");
        int qty = readInt();
        int area = askArea();
        if (area < 0) return;

        Order o;
        const char *error = createOrder(user.getId(), user.getName(), row, qty, area, o);
        if (error) { printf("%s\n", error); return; }
        printf("\nOrder placed successfully!\n"
               "Order ID        : %d\n"
               "Item            : %d x %s\n"
               "Total           : Rs %.2f\n"
               "Delivering to   : %s\n"
               "Distance        : %.1f km\n"
               "Route           : %s\n"
               "Traffic now     : %s\n"
               "Delivery time   : about %d minutes\n"
               "The store manager has been notified.\n",
               o.id, o.quantity, o.productName, o.total, DeliveryMap::areaName(o.area),
               o.km, o.route, o.traffic, o.etaMinutes);
    }

    // [OWNER: Aman]
    void showMyOrders(const User &user) const {
        bool found = false;
        printf("\n--- YOUR ORDERS ---\n");
        for (int i = 0; i < orderCount; ++i) {
            const Order &o = orders[i];
            if (o.customerId != user.getId()) continue;
            found = true;
            printf("Order #%d | %d x %s | Rs %.2f | %s", o.id, o.quantity, o.productName, o.total,
                   STATUS_NAMES[o.status]);
            if (o.status == PENDING || o.status == OUT_FOR_DELIVERY)
                printf(" | %.1f km | ETA about %d min (traffic: %s)", o.km, o.etaMinutes, o.traffic);
            printf("\n");
        }
        if (!found) printf("You have not placed any orders yet.\n");
    }

    // [OWNER: Aman]
    void cancelMyOrder(const User &user) {
        bool any = false;
        printf("\n--- YOUR PENDING ORDERS (can be cancelled) ---\n");
        for (int i = 0; i < orderCount; ++i)
            if (orders[i].customerId == user.getId() && orders[i].status == PENDING) {
                printf("#%d | %d x %s | Rs %.2f\n", orders[i].id, orders[i].quantity,
                       orders[i].productName, orders[i].total);
                any = true;
            }
        if (!any) { printf("You have no pending orders to cancel.\n"); return; }

        printf("Enter order ID to cancel (0 to go back): ");
        int id = readInt();
        if (id == 0) return;
        Order *o = findOrder(id);
        if (!o || o->customerId != user.getId()) { printf("Order not found in your pending orders.\n"); return; }
        if (o->status != PENDING) {
            printf("This order can no longer be cancelled (status: %s).\n", STATUS_NAMES[o->status]);
            return;
        }
        o->status = CANCELLED;
        inventory.restock(o->productName, o->domain, o->quantity);
        saveOrders();
        logCancellation(*o);
        notify("ORDER CANCELLED #%d by %s: %d x %s", o->id, o->customerName, o->quantity, o->productName);
        printf("Order #%d has been cancelled.\n", id);
    }

    // ---------- manager screens ----------
    // [OWNER: Atyushman]
    void addProduct() {
        printf("\n--- ADD PRODUCT / NEW STOCK ---\nCategory:");
        printDomainChoices();
        printf("  0. Cancel\nChoose: ");
        int d = readInt();
        if (d < 1 || d > DOMAIN_COUNT) { printf("Cancelled.\n"); return; }

        Item *item = makeItem(DOMAINS[d - 1], inventory.allocateId());
        char text[64];
        printf("Product name: ");  readLine(text, sizeof(text));  item->setName(text);
        printf("Quantity: ");      item->setQuantity(readInt());
        printf("Price (Rs): ");    item->setPrice(readDouble());
        printf("%s (e.g. size / pack / warranty): ", item->extraLabel());
        readLine(text, sizeof(text));
        item->setExtra(text);

        if (item->needsExpiry()) {
            printf("Expiry date (YYYY-MM-DD): ");
            readLine(text, sizeof(text));
            if (!isValidDate(text) || isExpired(text)) {
                printf("Invalid or already expired date. Product was not saved.\n");
                delete item;
                return;
            }
            item->setExpiry(text);
        }
        if (item->getName()[0] == '\0' || item->getQuantity() <= 0) {
            printf("Name must not be empty and quantity must be above 0. Product was not saved.\n");
            delete item;
            return;
        }

        char label[NAME_LEN + DOMAIN_LEN + 8];
        snprintf(label, sizeof(label), "%s (%s)", item->getName(), item->domain());
        int id = item->getId();
        inventory.add(item);                 // the inventory now owns the item
        inventory.save();
        printf("Saved: %s as batch ID %d. Customers will see it A-Z.\n", label, id);
    }

    // [OWNER: Atyushman]
    void deleteProduct() {
        inventory.showInternal();
        printf("\nEnter batch ID to DELETE (0 to cancel): ");
        int id = readInt();
        if (id == 0) return;
        printf("Are you sure you want to delete batch %d? (1 = yes, 0 = no): ", id);
        if (readInt() != 1) { printf("Cancelled.\n"); return; }
        printf(inventory.removeById(id) ? "Batch %d deleted.\n" : "Batch ID %d not found.\n", id);
    }

    // [OWNER: Nikhil]
    void showReport() {
        printf("\n--- LOW STOCK (%d or fewer) ---\n", LOW_STOCK_LIMIT);
        CatalogRow rows[MAX_CATALOG];
        int n = inventory.catalog("", rows, MAX_CATALOG);
        bool any = false;
        for (int i = 0; i < n; ++i) {
            if (rows[i].quantity == 0) {
                printf("OUT OF STOCK: %s (%s)\n", rows[i].name, rows[i].domain); any = true;
            } else if (rows[i].quantity <= LOW_STOCK_LIMIT) {
                printf("LOW STOCK: %s (%s) - %d left\n", rows[i].name, rows[i].domain, rows[i].quantity); any = true;
            }
        }
        if (!any) printf("None.\n");

        printf("\nShow items expiring within how many days? (e.g. 7): ");
        int days = readInt();
        if (days < 0) days = 0;
        printf("\n--- EXPIRY REPORT (expired + expiring within %d day(s)) ---\n", days);
        if (!inventory.printExpiryReport(days)) printf("No items are going to expire in this period.\n");
    }

    // [OWNER: Nikhil]
    void showStoreSummary() {
        int pending = 0, low = 0, out = 0;
        for (int i = 0; i < orderCount; ++i) if (orders[i].status == PENDING) ++pending;
        CatalogRow rows[MAX_CATALOG];
        int n = inventory.catalog("", rows, MAX_CATALOG);
        for (int i = 0; i < n; ++i) {
            if (rows[i].quantity == 0) ++out;
            else if (rows[i].quantity <= LOW_STOCK_LIMIT) ++low;
        }
        printf("Store status -> pending orders: %d | low stock: %d | out of stock: %d | "
               "expiring soon: %d | expired: %d\n", pending, low, out,
               inventory.countExpiringSoon(), inventory.countExpired());
    }

    // [OWNER: Aman]
    void alertsInbox() {
        while (true) {
            notifications.showNewestFirst();
            notifications.markAllSeen();
            notifications.saveToFile();
            if (notifications.empty()) return;
            printf("\n1. Pop newest alert (remove it)  2. Clear all alerts  3. Back\nChoose: ");
            int c = readInt();
            if (c == 1) {
                char text[NOTIF_LEN];
                notifications.pop(text, sizeof(text));
                notifications.saveToFile();
                printf("Removed: %s\n", text);
            } else if (c == 2) {
                notifications.clear();
                notifications.saveToFile();
                printf("All alerts cleared.\n");
                return;
            } else return;
        }
    }

    // [OWNER: Aman]
    void showOrders() const {
        if (orderCount == 0) { printf("No orders yet.\n"); return; }
        printf("\n--- ALL ORDERS ---\n");
        for (int i = 0; i < orderCount; ++i) {
            const Order &o = orders[i];
            printf("#%d | %s | %d x %s | Rs %.2f | %s | %s | delivery ~%d min (traffic: %s)\n",
                   o.id, o.customerName, o.quantity, o.productName, o.total,
                   DeliveryMap::areaName(o.area), STATUS_NAMES[o.status], o.etaMinutes, o.traffic);
        }
    }

    // [OWNER: Aman]
    void showCancelledOrders() const {
        printf("\n--- CANCELLED ORDERS (cancelled by customers) ---\n");
        FILE *in = fopen(CANCELLED_FILE, "r");
        bool any = false;
        char line[LINE_LEN];
        while (in && fgets(line, sizeof(line), in)) {
            stripNewline(line);
            char *p[9];
            if (splitLine(line, p, 9) < 9) continue;
            printf("#%s | %s | %s x %s (%s) | Rs %s | area: %s | cancelled on %s\n",
                   p[0], p[2], p[5], p[3], p[4], p[6], p[7], p[8]);
            any = true;
        }
        if (in) fclose(in);
        if (!any) printf("No cancelled orders.\n");
    }

    // [OWNER: Aman]
    void processNextOrder() {
        int id;
        while (orderQueue.dequeue(id)) {
            Order *o = findOrder(id);
            if (!o || o->status != PENDING) continue;      // stale (e.g. cancelled): try the next one
            o->status = OUT_FOR_DELIVERY;
            saveOrders();
            printf("\nProcessing oldest queued order (FIFO):\n"
                   "Order #%d | %s | %d x %s | Rs %.2f\n"
                   "Deliver to      : %s\n"
                   "Distance        : %.1f km\n"
                   "Route           : %s\n"
                   "Traffic         : %s\n"
                   "Time it will take: about %d minutes\n",
                   o->id, o->customerName, o->quantity, o->productName, o->total,
                   DeliveryMap::areaName(o->area), o->km, o->route, o->traffic, o->etaMinutes);
            return;
        }
        printf("No pending orders in the queue.\n");
    }

    // [OWNER: Aman]
    void markDelivered() {
        bool any = false;
        printf("\n--- ORDERS NOT DELIVERED YET ---\n");
        for (int i = 0; i < orderCount; ++i)
            if (orders[i].status == PENDING || orders[i].status == OUT_FOR_DELIVERY) {
                printf("#%d | %s | %d x %s | %s\n", orders[i].id, orders[i].customerName,
                       orders[i].quantity, orders[i].productName, STATUS_NAMES[orders[i].status]);
                any = true;
            }
        if (!any) { printf("Nothing to deliver.\n"); return; }
        printf("Enter order ID to mark DELIVERED (0 to cancel): ");
        int id = readInt();
        if (id == 0) return;
        Order *o = findOrder(id);
        if (!o || (o->status != PENDING && o->status != OUT_FOR_DELIVERY)) { printf("Order ID not found.\n"); return; }
        o->status = DELIVERED;
        saveOrders();
        printf("Order #%d marked DELIVERED.\n", id);
    }

    // [OWNER: Rahil]
    void simulateRush() {
        printf("How many random customer orders should be generated (1-10)? ");
        int n = readInt();
        if (n < 1 || n > 10) { printf("Please choose between 1 and 10.\n"); return; }
        printf("\n--- SIMULATED RUSH ---\n");
        for (int i = 0; i < n; ++i) {
            CatalogRow all[MAX_CATALOG], inStock[MAX_CATALOG];
            int total = inventory.catalog("", all, MAX_CATALOG), m = 0;
            for (int k = 0; k < total; ++k) if (all[k].quantity > 0) inStock[m++] = all[k];
            if (m == 0) { printf("Nothing left in stock.\n"); break; }

            const CatalogRow &row = inStock[rand() % m];
            int cap = row.quantity < 3 ? row.quantity : 3;
            int qty = 1 + rand() % cap;
            int area = rand() % AREA_COUNT;
            char who[24];
            snprintf(who, sizeof(who), "Guest-%d", ++guestCounter);

            Order o;
            const char *error = createOrder(0, who, row, qty, area, o);
            if (error) { printf("%s\n", error); break; }
            printf("%s ordered %d x %s -> %s | ~%d min | traffic: %s\n", who, qty, row.name,
                   DeliveryMap::areaName(area), o.etaMinutes, o.traffic);
        }
        printf("Check the pop-up / Alerts inbox for what happened.\n");
    }

    // [OWNER: Rahil]
    void trafficReport() {
        roads.refreshTraffic();
        roads.showReport();
    }

    // [OWNER: Aman]
    void removeExpiredStock() {
        int n = inventory.removeExpired();
        if (n) printf("Removed %d expired batch(es).\n", n);
        else   printf("No expired stock to remove.\n");
    }

    // ---------- menus (polymorphic: User& calls the right showDashboard) ----------
    // [OWNER: Omkar]
    void customerMenu(const User &user) {
        while (true) {
            user.showDashboard();
            printf("1. Browse products (A-Z)\n2. Search product\n3. Check delivery time\n"
                   "4. Place order\n5. My orders\n6. Cancel an order\n7. Logout\nChoose: ");
            switch (readInt()) {
                case 1: browseProducts(); break;
                case 2: searchProducts(); break;
                case 3: checkDeliveryTime(); break;
                case 4: placeOrder(user); break;
                case 5: showMyOrders(user); break;
                case 6: cancelMyOrder(user); break;
                case 7: return;
                default: printf("Invalid choice.\n");
            }
        }
    }

    // [OWNER: Omkar]
    void managerMenu(const User &user) {
        while (true) {
            user.showDashboard();
            showStoreSummary();
            notifications.showPopup();
            notifications.saveToFile();
            printf("\n 1. View inventory (internal expiry order)\n"
                   " 2. Add product / new stock\n"
                   " 3. Delete product / batch\n"
                   " 4. Expiry and low-stock report\n"
                   " 5. Alerts inbox (stack)\n"
                   " 6. View all orders\n"
                   " 7. View cancelled orders\n"
                   " 8. Process next order (FIFO)\n"
                   " 9. Mark order delivered\n"
                   "10. Live traffic report\n"
                   "11. Simulate random customer rush\n"
                   "12. Remove expired stock\n"
                   "13. Create staff (manager) account\n"
                   "14. Logout\nChoose: ");
            switch (readInt()) {
                case 1: inventory.showInternal(); break;
                case 2: addProduct(); break;
                case 3: deleteProduct(); break;
                case 4: showReport(); break;
                case 5: alertsInbox(); break;
                case 6: showOrders(); break;
                case 7: showCancelledOrders(); break;
                case 8: processNextOrder(); break;
                case 9: markDelivered(); break;
                case 10: trafficReport(); break;
                case 11: simulateRush(); break;
                case 12: removeExpiredStock(); break;
                case 13: registerUser("MANAGER"); break;
                case 14: return;
                default: printf("Invalid choice.\n");
            }
        }
    }

    // [OWNER: Omkar]
    void loginPage(const char *role) {
        bool isManager = strcmp(role, "MANAGER") == 0;
        printf(isManager ? "\n=============== MANAGER LOGIN ===============\n"
                         : "\n=============== CUSTOMER LOGIN ==============\n");
        char username[32], password[32];
        printf("Username: "); readLine(username, sizeof(username));
        printf("Password: "); readLine(password, sizeof(password));

        UserRecord *rec = authenticate(username, password);
        if (!rec) { printf("\nLogin failed. Check your username and password.\n"); return; }
        if (strcmp(rec->role, role) != 0) {
            printf("\nThis is %s account. Please use the %s login instead.\n",
                   isManager ? "not a manager" : "a manager", isManager ? "Customer" : "Manager");
            return;
        }
        printf("\nLogin successful!\n");
        if (isManager) { Manager m(*rec);  managerMenu(m); }
        else           { Customer c(*rec); customerMenu(c); }
    }

public:
    // [OWNER: SHARED (Omkar owns; others add startup lines)]
    StockLink() : orders(NULL), orderCount(0), orderCap(0), users(NULL), userCount(0), userCap(0),
                  nextOrderId(1), nextUserId(1), guestCounter(0) {
        loadUsers();
        if (!inventory.load()) inventory.seedDefaults();     // predefined store on first run
        loadOrders();
        notifications.loadFromFile();
        for (int i = 0; i < orderCount; ++i)
            if (orders[i].status == PENDING) orderQueue.enqueue(orders[i].id);
    }

    // [OWNER: SHARED (Omkar owns; others add save/free lines)]
    ~StockLink() {
        inventory.save();
        saveOrders();
        saveUsers();
        notifications.saveToFile();
        free(orders);
        free(users);
    }

    StockLink(const StockLink &) = delete;
    StockLink &operator=(const StockLink &) = delete;

    // [OWNER: Omkar]
    void run() {
        while (true) {
            printf("\n====================================================\n"
                   "              S T O C K L I N K   v4\n"
                   "       Food | Electronics | Clothing | Delivery\n"
                   "====================================================\n"
                   "1. Customer login\n2. Manager login\n3. Create customer account\n4. Exit\nChoose: ");
            int choice = readInt();
            if (choice == 1) loginPage("CUSTOMER");
            else if (choice == 2) loginPage("MANAGER");
            else if (choice == 3) registerUser("CUSTOMER");
            else if (choice == 4) { printf("Thank you for using StockLink. Goodbye!\n"); break; }
            else printf("Invalid choice. Try again.\n");
        }
    }
};

// [OWNER: Omkar]
int main() {
    srand((unsigned)time(NULL));
    StockLink app;                   // destructor saves everything, even on EOF
    try {
        app.run();
    } catch (const InputClosed &) {
        printf("\nInput closed. Saving data and exiting.\n");
    }
    return 0;
}
